import Lake
open Lake DSL

/- All nine dependencies are authenticated revision archives, locked by
   environment/baseline.json and the source receipts. Lake uses only relative
   paths; no Git revision is fabricated for an archive. -/
package sharpCut

require mathlib from ".lake/packages/mathlib"

lean_lib Khachiyan where
  srcDir := "vendor/khachiyan"

@[default_target]
lean_lib SharpCut
