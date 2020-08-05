import os
slit = '"" " " "BRD" "DRS" "LDS" "Branding" "Direct Response" "Leads" "=" "/" "in" "_" "9" "." "microsoft" "windows" "apple" "mac" "-" "1" "2" "3" "4" "5" "6" "7" "8" "0" "," "<" ">" "/n" "%" "b" "apple" "bananas" "strawberries" "oranges" "LLC" "Inc" "Corporation" "Enterprises" "Company" "(" ")" "+" "name" ","\n'
blit = '-1 1 2 3 4 5 6 7 8 9 0\n'
files = [i for i in os.listdir("/home/shraddha/Desktop/partialcorrectness/src/test/benchmarks/euphony/") if i.endswith("sl")]
#print(files)
print("h")
for file in files:
    with open(file, 'r') as f:
        # read a list of lines into data
        data = f.readlines()
        data[6] = slit
        data[15] = blit
    newfile = str(file).replace('.sl','') + "modified.sl"
    with open("/home/shraddha/Desktop/partialcorrectness/src/test/benchmarks/euphony/%s".format(newfile), 'w') as f:
        f.writelines(data)

