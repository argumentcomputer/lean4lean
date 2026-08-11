import Lean4Lean.Verify.TypeChecker.IsDefEq

/-!
# Conditional structure-eta checker surface

The executable checker roots remain at the L4L-15B upstream semantic gate.
These guards pin the proof-complete conditional bridge: host metadata must
resolve to a registered structure artifact and the Theory environment must
supply the missing reconstruction equality explicitly.
-/

namespace Lean4Lean.Tests.StructureEtaCapability

open Lean4Lean.TypeChecker.Inner

#check VEnv.HasStructureEta
#check StructureEtaArtifact
#check StructureEtaReady
#check tryEtaStructCore.WF_of_structureEta
#check isDefEqUnitLike.WF_of_structureEta

/--
info: 'Lean4Lean.VEnv.HasStructureEta' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.HasStructureEta

/--
info: 'Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF_of_structureEta' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.Expr.eqv_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.PersistentArray.toList'_push,
 Lean.Syntax.structEq_eq,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms tryEtaStructCore.WF_of_structureEta

/--
info: 'Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF_of_structureEta' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentArray.toList'_push,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms isDefEqUnitLike.WF_of_structureEta

end Lean4Lean.Tests.StructureEtaCapability
