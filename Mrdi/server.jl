using Oscar

function echo()
    input = IOBuffer(readline())
    # we can't use "load(stdin)" cause it probably would wait for the stream to finish. but we only want the next line
    val = load(input)
    save(stdout, val)
    # the next line is necessary cause we want to read a line in lean
    println("")
end

function matrix_inverse()
    input = IOBuffer(readline())
    # we can't use "load(stdin)" cause it probably would wait for the stream to finish. but we only want the next line
    A = load(input)
    A_inv = inv(A)
    save(stdout, A_inv)
    # the next line is necessary cause we want to read a line in lean
    println("")
end

function perm_group_membership()
    input = IOBuffer(readline())
    # we can't use "load(stdin)" cause it probably would wait for the stream to finish. but we only want the next line
    l = load(input)
    g = l[1]
    gens = l[2:end]
    # check how to get the group correctly
    G = permutation_group(5, gens)
    epi = epimorphism_from_free_group(G)
    g_free = preimage(epi, g)
    save(stdout, g_free)
    # the next line is necessary cause we want to read a line in lean
    println("")
end

function kbmag()
    GAP.Packages.load("kbmag", install=true)
    g = IOBuffer(readline())
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

    GAP.Globals.MakeConfluent(rws)
    println("finished")
end

function check_input_and_execute()
    while true
        try 
            cmd = readline()

            if cmd == "exit"
                break
            elseif cmd == "start server"
                println("server started")
            elseif cmd == "echo"
                echo()
            elseif cmd == "matrix inverse"
                matrix_inverse()
            elseif cmd == "perm group membership"
                perm_group_membership()
            elseif cmd == "kbmag"
                kbmag()
            else
                println("Input doesn't match the specified string.")
            end
        catch err
            println("Error: ", err)
        end
    end
end

check_input_and_execute()
