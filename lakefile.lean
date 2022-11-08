import Lake
open Lake DSL

package Categories {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib Categories
