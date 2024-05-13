using Oscar

# R, x = QQ["x"]
# p = 3 * x^2 - x + 1
# s = "teststring"
# z = ZZ(42)
# q = QQ(1//3)
# S5 = symmetric_group(5)
# perm = S5(cperm([4,2,3]))
# epi = epimorphism_from_free_group(S5) # cant be saved
# g_word = preimage(epi, perm) 
# matrix = [QQ(1) QQ(2); QQ(3) QQ(4)]
# vector = Vector([1, 2, 3])
# matrix_inv = inv(matrix)
# F = free_group(2)
# (f1, f2) = gens(F)
# (quot, proj) = quo(F, [f1^2, f2^2, comm(f1, f2)])
# rels = relators(quot)

# file = "fp_group_rels"
# save("mrdi-files/$file.mrdi", rels)
# x = load("mrdi-files/$file.mrdi")
# println(x)

# rw system
GAP.Packages.load("kbmag", install=true)
# f = free_group(2)
# rels = [comm(f[1], f[2]) / f[1], comm(f[2], f[1]) / f[2]]
# g = quo(f, rels)[1]
# save("test.mrdi", g)
# g = load("test.mrdi")
g = load("mrdi-files/fpgrouptest2.mrdi")
GAP.Globals.g = g
generators = gens(g)
GAP.Globals.generators = generators
rws = GAP.Globals.KBMAGRewritingSystem(GAP.GapObj(g))

# The only change is 
# callstring := Concatenation(Filename(_KBExtDir,"kbprog"),"  ",_KBTmpFileName);
# to 
# callstring := Concatenation(Filename(_KBExtDir,"kbprog")," -ve ",_KBTmpFileName);
# This change leads to print messages during MakeConfluent
GAP.evalstr_ex("""
KBRWS := function ( rws )
    local O, callstring;
    if not IsKBMAGRewritingSystemRep(rws)  then
        Error("First argument is not a rewriting system.");
    fi;
    if IsConfluentRWS(rws) then
        Print("#The rewriting system is already confluent.\\n");
        Print("#Call - ResetRWS(<rws>) to restart.\\n");
        return fail;
    fi;
    #If we have already run KBRWS then the original equations will
    #have been kept and should be re-inserted.
    AddOriginalEqnsRWS(rws);
    #Keep the original equations, in case we want them again.
    if not IsBound(rws!.originalEquations) then
        rws!.originalEquations := StructuralCopy(rws!.equations);
    fi;
    WriteRWS(rws,_KBTmpFileName);
    callstring := Concatenation(Filename(_KBExtDir,"kbprog")," -ve ",_KBTmpFileName);
    Info(InfoRWS,1,"Calling external Knuth-Bendix program.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    UpdateRWS(rws,_KBTmpFileName,true);
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    Info(InfoRWS,1,"External Knuth-Bendix program complete.");
    
    if rws!.isConfluent then
        O := rws!.options;
        if IsBound(O.maxstoredlen) or IsBound(O.maxoplen) then
        Print(
            "#WARNING: Because of the control parameters you set, the system may\\n");
        Print(
            "#         not be confluent. Unbind the parameters and re-run KnuthBendix\\n");
        Print(
            "#         to check!\\n");
        rws!.isConfluent:=false;
        fi;
    fi;
    if rws!.isConfluent then
        Info(InfoRWS,1,"System computed is confluent.");
        rws!.isAvailableNormalForm := true;
        rws!.warningOn := false;
    else
        Info(InfoRWS,1,"System computed is NOT confluent.");
        rws!.isAvailableNormalForm := false;
        rws!.warningOn := true;
    fi;
    rws!.KBRun := true;
    rws!.isAvailableReduction := true;
    rws!.isAvailableSize := true;
    return rws!.isConfluent;
end;;
""")

pipe = Pipe()
event = Base.Event()
# We want do intercept the messages printed my MakeConfluent.
# This is asynchronous so the writer doesn't get stuck if the pipe is full.
writer = @async redirect_stdout(pipe) do
    notify(event)
    confluent = GAP.Globals.MakeConfluent(rws)
    close(Base.pipe_writer(pipe))
    if !confluent
        error("Failed to make the rws confluent")
    end
end

# Waiting for the event ensures that the reader doesn't start before we have some output
wait(event)
rws = read(pipe, String)
wait(writer)
rws = replace(rws, "IdWord" => "One(g)")
rws = replace(rws, "->" => "=")
# Delete everything after the substring
substring = "#Search for overlaps is complete."
pattern = Regex("(?s)" * substring * ".*")
rws = replace(rws, pattern => "")
# Split lines and delete all empty lines
lines = filter(x -> !isempty(x), split(rws, '\n'))
# Delete everything before '#' in every line
lines = map(line -> replace(line, r"^.*?#" => ""), lines)
result = Tuple{Int, Bool, Int, Int, FPGroupElem, FPGroupElem}[]
# We don't start at 1 cause the first equations will be trivial
for i in range(1 + 4 * length(generators), length=length(lines) ÷ 2 - 2 * length(generators), step=2)
    equation = lines[i + 1]
    for j in range(1, length=length(generators))
        equation = replace(equation, "_g" * string(2 * j - 1) => "generators[$j]")
        equation = replace(equation, "_g" * string(2 * j) => "(generators[$j]^-1)")
    end
    words = split(equation, "=")
    lhs_string = String(words[1])
    rhs_string = String(words[2])
    (success_lhs, lhs, _, _, _) = GAP.evalstr_ex(lhs_string * ";;")[1]
    (success_rhs, rhs, _, _, _) = GAP.evalstr_ex(rhs_string * ";;")[1]
    if !(success_lhs && success_rhs)
        error("failed to evaluate words in GAP:\n " * lhs_string * ",\n" * rhs_string)
    end
    new_equation = occursin("New equation" ,lines[i])
    matches = collect(eachmatch(r"\d+", lines[i]))
    if length(matches) < 1
        error("line should contain equation number. line is ", line[i])
    end
    equation_number = parse(Int, matches[1].match)
    if new_equation
        if length(matches) < 3
            error("expected 3 values: number of the equation and two overlaps. line is ", lines[i])
        end
        overlap1 = parse(Int, matches[2].match)
        overlap2 = parse(Int, matches[3].match)
        push!(result, (equation_number, new_equation, overlap1, overlap2, lhs, rhs))
    else
        push!(result, (equation_number, new_equation, 0,        0,        lhs, rhs))
    end
end
save("kbmag.mrdi", result)
