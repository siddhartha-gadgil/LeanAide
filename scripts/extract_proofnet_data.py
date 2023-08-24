import jsonlines

def extract_proofnet_lines(file:str):
    with jsonlines.open(file + ".jsonl", "r") as data:
        nl_statements = [line["nl_statement"] + '\n' for line in data]

    with open(file + "_statements" + ".txt", "w") as output:
        output.writelines(nl_statements)

extract_proofnet_lines("../data/proofnet_test")
extract_proofnet_lines("../data/proofnet_valid")