import Lake
open Lake DSL

package Categories {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib Categories
