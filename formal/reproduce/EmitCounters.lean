import UniformK60.SequentialCounter

open UniformK60.SequentialCounter

def main (args : List String) : IO Unit := do
  let input ← IO.FS.readFile args[0]!
  let mut output : Array String := #[]
  for line in input.splitOn "\n" do
    if line.isEmpty then continue
    let numbers := (line.splitOn " ").map String.toNat!
    let top := numbers[0]!
    let bound := numbers[1]!
    let atoms := (numbers.drop 2).toArray
    output := output.push ("c counter " ++ toString (finalTop atoms.size bound top))
    for clause in counter (fun i => atoms[i]!) atoms.size bound top do
      let literals := clause.map fun (sign, atom) =>
        (if sign then "" else "-") ++ toString atom
      output := output.push (String.intercalate " " literals ++ " 0")
  IO.FS.writeFile args[1]! (String.intercalate "\n" output.toList ++ "\n")
