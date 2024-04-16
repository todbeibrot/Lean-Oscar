# I can't install Oscar on windows. So for debugging purpose I use this "server". It will just echo the incoming data.

function echo()
    try
        input = readline()
        println(input)
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
        else
            echo()
        end
    end
end

check_input_and_execute()
