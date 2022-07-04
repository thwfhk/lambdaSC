import os

codeString = open("./CodeString.hs", "w")

def oneline(s):
  if s == "":
    return "  \\ \\n\\\n"
  else:
    return "  \\" + s.replace("\\", "\\\\").replace("\"", "\\\"") + " \\n\\\n"

def string2haskell(name, s):
  ls = s.split("\n")
  ls = "".join (list (map (oneline, ls)))
  ls = name + " = \"\\\n" + ls +"  \\\""
  return ls

output = "module CodeString where\n\n"

for fileName in os.listdir("./test"):
  if fileName == "examples.sc":
    continue
  f = open("./test/" + fileName, "r")
  s = f.read()
  output = output + string2haskell(fileName[:-3], s) + "\n\n"

codeString.write(output)
