import Batteries

/-!
# Standard Library and Batteries

Code examples for IO operations, Batteries, and the package ecosystem.
-/

namespace ZeroToQED.StdLibrary

-- ANCHOR: io_basics
-- Basic IO operations
def ioDemo : IO Unit := do
  -- Print to stdout
  IO.println "Hello, world!"
  IO.print "No newline"
  IO.println ""  -- newline

  -- Environment variables
  let path ← IO.getEnv "PATH"
  IO.println s!"PATH exists: {path.isSome}"

  -- Current time (milliseconds since epoch)
  let now ← IO.monoMsNow
  IO.println s!"Timestamp: {now}"

  -- Random numbers
  let rand ← IO.rand 1 100
  IO.println s!"Random 1-100: {rand}"
-- ANCHOR_END: io_basics

-- ANCHOR: file_io
-- File operations
def fileDemo : IO Unit := do
  let testFile := "test_output.txt"

  -- Write to file
  IO.FS.writeFile testFile "Line 1\nLine 2\nLine 3\n"

  -- Read entire file
  let contents ← IO.FS.readFile testFile
  IO.println s!"Contents:\n{contents}"

  -- Read as lines
  let lines ← IO.FS.lines testFile
  IO.println s!"Number of lines: {lines.size}"
  for line in lines do
    IO.println s!"  > {line}"

  -- Clean up
  IO.FS.removeFile testFile
-- ANCHOR_END: file_io

-- ANCHOR: directory_io
-- Directory operations
def directoryDemo : IO Unit := do
  -- Current working directory
  let cwd ← IO.currentDir
  IO.println s!"Current directory: {cwd}"

  -- List directory contents
  let entries ← System.FilePath.readDir "."
  IO.println s!"Files in current directory: {entries.size}"

  -- Print first few entries
  for entry in entries.toList.take 5 do
    IO.println s!"  {entry.fileName}"
-- ANCHOR_END: directory_io

-- ANCHOR: process_io
-- Running external processes
def processDemo : IO Unit := do
  -- Run a command and capture output
  let output ← IO.Process.output {
    cmd := "echo"
    args := #["Hello from subprocess"]
  }
  IO.println s!"Exit code: {output.exitCode}"
  IO.println s!"stdout: {output.stdout}"

  -- Check if command succeeded
  if output.exitCode == 0 then
    IO.println "Command succeeded"
  else
    IO.println s!"Command failed: {output.stderr}"
-- ANCHOR_END: process_io

-- ANCHOR: batteries_heap
-- BinaryHeap: priority queue with O(log n) push/pop
def heapDemo : IO Unit := do
  -- Max-heap (largest first with >)
  let heap := Batteries.BinaryHeap.empty (α := Nat) (lt := (· > ·))
    |>.insert 5
    |>.insert 1
    |>.insert 3
    |>.insert 9

  IO.println s!"heap max: {heap.max}"  -- some 9

  -- Pop the max element
  let (maxVal, heap') := heap.extractMax
  IO.println s!"extracted: {maxVal}"   -- some 9
  IO.println s!"new max: {heap'.max}"  -- some 5
-- ANCHOR_END: batteries_heap

-- ANCHOR: batteries_rbmap
-- RBMap: ordered map with O(log n) operations
def rbmapDemo : IO Unit := do
  -- Create a map with String keys, Nat values
  let scores : Batteries.RBMap String Nat compare :=
    Batteries.RBMap.empty
      |>.insert "alice" 95
      |>.insert "bob" 87
      |>.insert "carol" 92

  -- Lookup
  let aliceScore := scores.find? "alice"
  let daveScore := scores.find? "dave"
  IO.println s!"alice: {aliceScore}"  -- some 95
  IO.println s!"dave: {daveScore}"    -- none

  -- Convert to list for display (sorted by key)
  IO.println s!"all: {scores.toList}"
-- ANCHOR_END: batteries_rbmap

-- ANCHOR: batteries_unionfind
-- UnionFind: disjoint set with near O(1) union/find
def unionFindDemo : IO Unit := do
  -- Create structure and add 5 elements (indices 0-4)
  let uf := Batteries.UnionFind.empty
    |>.push |>.push |>.push |>.push |>.push

  -- Union 0 with 1, and 2 with 3
  let uf := uf.union! 0 1
  let uf := uf.union! 2 3

  -- Check if elements are in same set (same root)
  let root0 := uf.rootD 0
  let root1 := uf.rootD 1
  let root2 := uf.rootD 2
  let root4 := uf.rootD 4

  IO.println s!"0 and 1 same set: {root0 == root1}"  -- true
  IO.println s!"0 and 2 same set: {root0 == root2}"  -- false
  IO.println s!"4 alone: {root4 == 4}"               -- true
-- ANCHOR_END: batteries_unionfind

-- ANCHOR: batteries_dlist
-- DList: difference list with O(1) append
def dlistDemo : IO Unit := do
  -- Build a list by repeated appending
  -- With regular List, this would be O(n^2), with DList it's O(n)
  let d1 : Batteries.DList Nat := Batteries.DList.singleton 1
  let d2 := d1.push 2
  let d3 := d2.push 3
  let d4 := d3.append (Batteries.DList.ofList [4, 5, 6])

  -- Convert back to List when done building
  let result := d4.toList
  IO.println s!"result: {result}"  -- [1, 2, 3, 4, 5, 6]
-- ANCHOR_END: batteries_dlist

-- ANCHOR: batteries_list_array
-- Batteries extends List and Array with useful functions
def batteriesListDemo : IO Unit := do
  let nums := [1, 2, 3, 4, 5]

  -- Chunking
  let chunks := nums.toChunks 2
  IO.println s!"toChunks 2: {chunks}"   -- [[1, 2], [3, 4], [5]]

  -- Rotating
  let rotL := nums.rotateLeft 2
  let rotR := nums.rotateRight 2
  IO.println s!"rotateLeft 2: {rotL}"   -- [3, 4, 5, 1, 2]
  IO.println s!"rotateRight 2: {rotR}"  -- [4, 5, 1, 2, 3]

  -- Partitioning
  let (small, big) := nums.partition (· ≤ 3)
  IO.println s!"partition: small={small}, big={big}"

  -- Erasure (remove first occurrence)
  let erased := nums.erase 3
  IO.println s!"erase 3: {erased}"       -- [1, 2, 4, 5]
-- ANCHOR_END: batteries_list_array

-- ANCHOR: practical_example
-- Practical example: word frequency counter
def countWords (text : String) : Std.HashMap String Nat :=
  let words := text.toLower.splitOn " "
    |>.map (fun w => w.toList.filter Char.isAlpha |> String.ofList)
    |>.filter (!·.isEmpty)
  words.foldl (fun map word =>
    map.insert word ((map.get? word).getD 0 + 1)
  ) {}

def wordFreqDemo : IO Unit := do
  let text := "The quick brown fox jumps over the lazy dog The dog barks"
  let freq := countWords text

  IO.println "Word frequencies:"
  let sorted := freq.toList.toArray
    |>.qsort (fun a b => a.2 > b.2)

  for (word, count) in sorted do
    IO.println s!"  {word}: {count}"
-- ANCHOR_END: practical_example

def main : IO Unit := do
  IO.println "=== IO Basics ==="
  ioDemo
  IO.println "=== File IO ==="
  fileDemo
  IO.println "=== Directory IO ==="
  directoryDemo
  IO.println "=== Process IO ==="
  processDemo
  IO.println "=== BinaryHeap ==="
  heapDemo
  IO.println "=== RBMap ==="
  rbmapDemo
  IO.println "=== UnionFind ==="
  unionFindDemo
  IO.println "=== DList ==="
  dlistDemo
  IO.println "=== List Extensions ==="
  batteriesListDemo
  IO.println "=== Word Frequency ==="
  wordFreqDemo

end ZeroToQED.StdLibrary
