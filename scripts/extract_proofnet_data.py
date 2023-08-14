import jsonlines

with jsonlines.open("../data/proofnet_test.jsonl", "r") as data:
    nl_statements = [line["nl_statement"] + '\n' for line in data]

with open("../data/proofnet_statements.txt", "w") as output:
    output.writelines(nl_statements)