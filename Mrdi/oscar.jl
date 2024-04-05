using Oscar
# TODO
# using Oscar might take a lot of time. 
# maybe we can reduce it by importing only the important parts of the library
using JSON

mrdi_test_file = "mrdi-files/test.mrdi"

# TODO
# can we turn stuff into mrdi without saving it?
# what can we turn into mrdi files?
# why does it need so much time for starting a julia file?
# save stuff in a file related to this file not to the project

if isempty(ARGS)
    x = 3
    save(mrdi_test_file, x)
elseif ARGS[1] == "testint"
    json_data = JSON.json(JSON.parsefile(mrdi_test_file))
    println(json_data)
elseif ARGS[1] == "echo"
    new_mrdi = load(stdin)
    save(stdout, new_mrdi)
else
    println("wrong command line arguments")
end