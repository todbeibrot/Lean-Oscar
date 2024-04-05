using Oscar

function echo()
    try
        input = IOBuffer(readline())
        # we can't use "load(stdin)" cause it probably would wait for the stream to finish. but we only want the next line
        val = load(input)
        save(stdout, val)
        # the next line is necessary cause we want to read a line in lean
        println("")
    catch err
        println("Error: ", err)
    end
end

function matrix_inverse()
    try
        input = IOBuffer(readline())
        # we can't use "load(stdin)" cause it probably would wait for the stream to finish. but we only want the next line
        A = load(input)
        A_inv = inv(A)
        save(stdout, A_inv)
        # the next line is necessary cause we want to read a line in lean
        println("")
    catch err
        println("Error: ", err)
    end
end

function permutation()
    try
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
    catch err
        println("Error: ", err)
    end
end

function check_input_and_execute()
    while true
        cmd = readline()

        if cmd == "exit"
            break
        elseif cmd == "start server"
            println("server started")
        elseif cmd == "echo"
            echo()
        elseif cmd == "matrix inverse"
            matrix_inverse()
        elseif cmd == "permutation"
            permutation()
        else
            println("Input doesn't match the specified string.")
        end
    end
end

check_input_and_execute()
