using JSON

filename = "../data/prompts.json"

prompts = JSON.parsefile(filename)

for prompt in prompts
    prompt["kind"] = "theorem"
end

open(filename, "w") do file 
    JSON.Writer.print(file, prompts)
end
