open Lean Meta Elab Command

public meta def auditDeclaration (name : Name) (captureProof : Bool) : CommandElabM Unit := do
  liftTermElabM do
    let info ← getConstInfo name
    let axioms ← Lean.collectAxioms name
    let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
    let edges ← if captureProof then do
      let some value := info.value? true | throwError "Missing source proof/body: {name}"
      pure (toJson (value.getUsedConstants.toList.map Name.toString))
    else pure Json.null
    let fullType := (← ppExpr info.type).pretty
    let canonical ← withOptions (fun o =>
      (o.setBool `pp.fullNames true).setBool `pp.notation false) do
      pure (← ppExpr info.type).pretty
    forallTelescope info.type fun xs conclusion => do
      let mut binders : Array Json := #[]
      for i in [:xs.size] do
        let decl ← xs[i]!.fvarId!.getDecl
        let kind := match decl.binderInfo with
          | .default => "explicit"
          | .implicit => "implicit"
          | .strictImplicit => "strict-implicit"
          | .instImplicit => "instance"
        binders := binders.push (Json.mkObj [
          ("index", toJson i), ("name", toJson decl.userName.toString),
          ("kind", toJson kind), ("is_proposition", toJson (← isProp decl.type)),
          ("type", toJson (← ppExpr decl.type).pretty)])
      let record := Json.mkObj [
        ("declaration", toJson name.toString), ("elaborated_type", toJson fullType),
        ("canonical_type", toJson canonical),
        ("binders", toJson binders), ("conclusion", toJson (← ppExpr conclusion).pretty),
        ("axioms", toJson (axioms.toList.map Name.toString)),
        ("direct_proof_dependencies", edges)]
      logInfo m!"AUDIT_DECLARATION {record.compress}"

elab "audit_decl " name:ident : command => auditDeclaration name.getId false
elab "audit_source_decl " name:ident : command => auditDeclaration name.getId true
