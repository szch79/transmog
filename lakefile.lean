import Lake

open Lake DSL System

require hazel from git "https://github.com/szch79/hazel.git" @ "v4.35.0-rc2"

abbrev options : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`autoImplicit, true⟩,
  ⟨`relaxedAutoImplicit, true⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩
]

abbrev linters : Array LeanOption := #[
  ⟨`linter.hazel, true⟩,
  ⟨`linter.hazel.docstring.missingDocstring, false⟩,
  ⟨`linter.hazel.style.redundantImplicitLevel, .ofNat 2⟩
]

package transmog where
  version := v!"0.1.0"
  leanOptions := options ++
    linters.map fun s => { s with name := `weak ++ s.name }

private def buildCpp (pkg : Package) (stem : String) : FetchM (Job FilePath) := do
  let oFile := pkg.buildDir / "ffi" / s!"{stem}.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi" / s!"{stem}.cpp"
  let headerJob ← inputTextFile <| pkg.dir / "ffi" / s!"{stem}.h"
  let srcJob := srcJob.zipWith (fun src _ => src) headerJob
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / "ffi").toString]
  let traceArgs := #[
    "-O3", "-DNDEBUG",
    "-fPIC",
    "-std=c++17",
  ]
  buildO oFile srcJob weakArgs traceArgs "clang++" getLeanTrace

target bytearray.o pkg : FilePath := buildCpp pkg "bytearray"

extern_lib libbytearray pkg := do
  let name := nameToStaticLib "bytearray"
  let job ← bytearray.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[job]

@[default_target]
lean_lib Transmog where
  precompileModules := true

@[lint_driver]
script lint args do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "Transmog"] ++ args.toArray
  }
  return ← child.wait

lean_lib TransmogTest where
  globs := #[.submodules `TransmogTest]

lean_exe transmogTests where
  root := `TransmogTest.Main

@[test_driver]
script test _args do
  for (cmd, args) in #[("lake", #["build", "Transmog", "TransmogTest", "Examples", "--wfail"]),
      ("lake", #["exe", "transmogTests"]),
      ("sh", #["TransmogTest/RuntimeRepr/check.sh"]),
      ("lake", #["-d", "tests/downstream", "build", "--wfail"]),
      ("lake", #["-d", "tests/downstream", "exe", "consumer"])] do
    let child ← IO.Process.spawn { cmd, args }
    let result ← child.wait
    if result != 0 then return result
  return 0

lean_lib Examples where
  globs := #[.submodules `Examples]
