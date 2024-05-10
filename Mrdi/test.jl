using Oscar
using JSON

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
println("start loading")
GAP.Packages.load("kbmag", install=true)
println(GAP.Packages.locate_package("kbmag"))
f = free_group(2)
(a, b) = gens(f)
rels = [comm(a, b) / a, comm(b, a) / b]
g = quo(f, rels)[1]
g2 = GAP.GapObj(g)
s = GAP.Globals.KBMAGRewritingSystem(g2)

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
writer = @async redirect_stdout(pipe) do
    GAP.Globals.MakeConfluent(s)
    close(Base.pipe_writer(pipe))
end

# Why do we need the next line???
println("read result")
s = read(pipe, String)
wait(writer)
s = replace(s, "IdWord" => "1")
s = replace(s, "->" => "=")

# Delete everything after the substring
substring = "#Search for overlaps is complete."
pattern = Regex("(?s)" * substring * ".*")
s = replace(s, pattern => "")

# Split lines and delete all empty lines
lines = filter(x -> !isempty(x), split(s, '\n'))
# Delete everything before '#' in every line
lines = map(line -> replace(line, r"^.*?#" => ""), lines)

# I want to have a Vector where every element consists of
# equation number, initial/overlap, two overlap numbers, equation

v = Tuple{Int, Bool, Int, Int, String}[]
for i in range(1, length=length(lines) ÷ 2, step=2)
    equation = lines[i + 1]
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
        push!(v, (equation_number, new_equation, overlap1, overlap2, equation))
    else
        push!(v, (equation_number, new_equation, 0, 0, equation))
    end
end

for element in v
    println(element)
end
