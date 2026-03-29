import LeanSce.Core.Syntax
import LeanSce.Core.BigStep
import LeanSce.Core.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.SCE.Elaboration

open SCE Core

theorem index_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {n : Nat}
    (h₁ : SLookup T n T₁)
    (h₂ : SLookup T n T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero A B => cases h₂; rfl
  | succ A B n C _ ih => cases h₂ with | succ _ _ _ _ h₂ => exact ih h₂

theorem record_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {l : String}
    (h₁ : SCE.SRLookup T l T₁)
    (h₂ : SCE.SRLookup T l T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero l T => cases h₂; rfl
  | andl A B l T _ h_cond ih =>
    cases h₂ with
    | andl _ _ _ _ h₂' _ => exact ih h₂'
    | andr _ _ _ _ h₂' h_cond₂ =>
      exact absurd (h_cond.1) h_cond₂.2
  | andr A B l T _ h_cond ih =>
    cases h₂ with
    | andr _ _ _ _ h₂' _ => exact ih h₂'
    | andl _ _ _ _ h₂' h_cond₂ =>
      exact absurd (h_cond.1) h_cond₂.2

theorem type_safe_index_lookup
    {ST₁ ST₂ : SCE.Typ} {n : Nat}
    (h : SLookup ST₁ n ST₂)
    : Core.Lookup (elabTyp ST₁) n (elabTyp ST₂) := by
  induction h with
  | zero A B => exact Core.Lookup.zero
  | succ A B n C _ ih => exact Core.Lookup.succ ih

theorem type_safe_label_existence
    {l : String} {ST : SCE.Typ}
    : SCE.LabelIn l ST ↔ Core.Lin l (elabTyp ST) := by
  constructor
  · intro h
    induction h with
    | rcd l T =>
      simp [elabTyp]
      exact Core.Lin.rcd
    | andl A B l _ ih =>
      simp [elabTyp]
      exact Core.Lin.andl ih
    | andr A B l _ ih =>
      simp [elabTyp]
      exact Core.Lin.andr ih
    | sig l T _ ih =>
      simp [elabTyp, elabModTyp]
      exact ih
  · intro h
    cases ST with
    | rcd lA T =>
      simp [elabTyp] at h
      cases h
      exact SCE.LabelIn.rcd l T
    | and A B =>
      simp [elabTyp] at h
      cases h with
      | andl h =>
        exact SCE.LabelIn.andl A B l (type_safe_label_existence.mpr h)
      | andr h =>
        exact SCE.LabelIn.andr A B l (type_safe_label_existence.mpr h)
    | int => simp [elabTyp] at h; cases h
    | top => simp [elabTyp] at h; cases h
    | arr _ _ => simp [elabTyp] at h; cases h
    | sig mt =>
      cases mt with
      | TyIntf T =>
        simp [elabTyp, elabModTyp] at h
        exact SCE.LabelIn.sig l T (type_safe_label_existence.mpr h)
      | TyArrM T mt' =>
        simp [elabTyp, elabModTyp] at h; cases h


theorem type_safe_label_nonexistence
    {l : String} {ST : SCE.Typ}
    : ¬ SCE.LabelIn l ST ↔ ¬ Core.Lin l (elabTyp ST) := by
  constructor
  · intro hns hc; exact hns (type_safe_label_existence.mpr hc)
  · intro hnc hs; exact hnc (type_safe_label_existence.mp hs)

theorem type_safe_record_lookup
    {ST₁ ST₂ : SCE.Typ} {l : String}
    (h : SCE.SRLookup ST₁ l ST₂)
    : Core.RLookup (elabTyp ST₁) l (elabTyp ST₂) := by
  induction h with
  | zero l T =>
    simp [elabTyp]
    exact Core.RLookup.zero
  | andl A B l T _ h_cond ih =>
    simp [elabTyp]
    exact Core.RLookup.landl ih
      (type_safe_label_nonexistence.mp h_cond.2)
  | andr A B l T _ h_cond ih =>
    simp [elabTyp]
    exact Core.RLookup.landr ih
      ⟨type_safe_label_nonexistence.mp h_cond.2,
       type_safe_label_existence.mp h_cond.1⟩

theorem inference_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : T₁ = T₂ := by
  revert T₂ ce₂
  induction h₁ with
  | equery =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | elit _ n =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eunit _ =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eapp _ a' _ _ _ ce1' ce2' h1' h2' =>
      have := ih1 h1'
      cases this; rfl
  | eproj ctx A B se ce i _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eproj _ a' _ _ ce' _ h' hlook' =>
      have hA := ih h'
      rw [hA] at hlook
      exact index_lookup_uniqueness hlook hlook'
  | ebox ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ebox _ en _ _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      rw [hA] at ih2
      exact ih2 h2'
  | edmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | edmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 (hA ▸ h2')
      rw [hA, hB]
  | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | enmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 h2'
      rw [hA, hB]
  | elam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elam _ _ b' _ ce' h' =>
      have hB := ih h'
      rw [hB]
  | erproj ctx A B se ce l _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | erproj _ a' b' _ ce' _ h' hlook' =>
      have hB := ih h'
      rw [hB] at hlook
      exact record_lookup_uniqueness hlook hlook'
  | eclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 (hA ▸ h2')
      rw [hB]
  | elrec ctx A se ce l _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elrec _ a' _ ce' _ h' =>
      have hA := ih h'
      rw [hA]
  | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | letb _ _ b' _ _ ce1' ce2' h1' h2' =>
      exact ih2 h2'
  | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | openm _ a' b' _ _ ce1' ce2' _ h1' h2' =>
      have hA : SCE.Typ.rcd l A = SCE.Typ.rcd _ a' := ih1 h1'
      cases hA
      exact ih2 h2'
  | mstruct ctx ctxInner B sb se ce envCore _ _ _ ih =>
    intros T₂ ce₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mstruct _ ci' b' _ _ ce' _ hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed =>
          rw [hs1 rfl, hs1' rfl]
        | open_ =>
          rw [hs2 rfl, hs2' rfl]
      rw [←hCtx] at h'
      have hB := ih h'
      rw [hB]
  | mfunctor ctx ctxInner A B sb se ce _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mfunctor _ ci' _ b' _ _ ce' hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hB := ih h'
      rw [hB]
  | mclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hA := ih1 h1'
      rw [← hA] at h2'
      have hB := ih2 h2'
      rw [hB]
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mapp _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hA := ih2 h2'
      have := ih1 h1'
      rw [hA] at this
      cases this; rfl
  | mlink ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlink _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have := ih2 h2'
      rw [hA] at this
      cases this
      rw [hA]

theorem elaboration_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : ce₁ = ce₂ := by
  revert T₂ ce₂
  induction h₁ with
  | equery =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | elit _ n =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eunit _ =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eapp _ a' _ _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 h2'
      rw [hA, hB]
  | eproj ctx A B se ce i _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eproj _ a' _ _ ce' _ h' hlook' =>
      have hA := ih h'
      rw [hA]
  | ebox ctx ctx' A se1 se2 ce1 ce2 h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ebox _ en _ _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | edmrg ctx A B se1 se2 ce1 ce2 h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | edmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hA := inference_uniqueness h1_orig h1'
      rw [← hA] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | enmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | elam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elam _ _ b' _ ce' h' =>
      have hce := ih h'
      rw [hce]
  | erproj ctx A B se ce l _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | erproj _ a' b' _ ce' _ h' hlook' =>
      have hce := ih h'
      rw [hce]
  | eclos ctx ctx' A B se1 se2 ce1 ce2 hval h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | elrec ctx A se ce l _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elrec _ a' _ ce' _ h' =>
      have hce := ih h'
      rw [hce]
  | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | letb _ _ b' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | openm ctx A B se1 se2 ce1 ce2 l h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | openm _ a' b' _ _ ce1' ce2' _ h1' h2' =>
      have htyp : SCE.Typ.rcd l A = SCE.Typ.rcd _ a' := inference_uniqueness h1_orig h1'
      cases htyp
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mstruct ctx ctxInner B sb se ce envCore _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mstruct _ ci' b' _ _ ce' _ hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hce := ih h'
      rw [hce]
  | mfunctor ctx ctxInner A B sb se ce _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mfunctor _ ci' _ b' _ _ ce' hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hce := ih h'
      rw [hce]
  | mclos ctx ctx' A B se1 se2 ce1 ce2 hval h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mapp _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mlink ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlink _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]

theorem elab_value
    {Γ A : SCE.Typ} {v : SCE.Exp} {cv : Core.Exp}
    (helab : elabExp Γ v A cv)
    (hval : SCE.Value v)
    : Core.Value cv := by
  induction hval generalizing Γ A cv with
  | vint =>
    cases helab
    exact Core.Value.vint
  | vunit =>
    cases helab
    exact Core.Value.vunit
  | vclos hv ih =>
    cases helab with
    | eclos _ _ _ _ _ _ ce1 ce2 _ h1 h2 =>
      exact Core.Value.vclos (ih h1)
  | vmclos hv ih =>
    cases helab with
    | mclos _ _ _ _ _ _ ce1 ce2 _ h1 h2 =>
      exact Core.Value.vclos (ih h1)
  | vmrg hv1 hv2 ih1 ih2 =>
    cases helab with
    | edmrg _ _ _ _ _ ce1 ce2 h1 h2 =>
      exact Core.Value.vmrg (ih1 h1) (ih2 h2)
  | vlrec hv ih =>
    cases helab with
    | elrec _ _ _ ce _ h =>
      exact Core.Value.vrcd (ih h)

theorem type_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (h : elabExp Γ es A ec)
    : HasType (elabTyp Γ) ec (elabTyp A) := by
    induction h with
    | equery =>
      exact HasType.tquery
    | elit ctx n =>
      simp [elabTyp]
      exact HasType.tint
    | eunit ctx =>
      simp [elabTyp]
      exact HasType.tunit
    | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tapp ih1 ih2
    | eproj ctx A B se ce i _ hlook ih =>
      exact HasType.tproj ih (type_safe_index_lookup hlook)
    | ebox ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tbox ih1 ih2
    | edmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      simp [elabTyp]
      exact HasType.tmrg ih1 ih2
    | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      simp [elabTyp]
      apply HasType.tapp
      · apply HasType.tlam
        apply HasType.tmrg
        · apply HasType.tbox
          · exact HasType.tproj HasType.tquery Lookup.zero
          · exact ih1
        · apply HasType.tbox
          · exact HasType.tproj HasType.tquery (Lookup.succ Lookup.zero)
          · exact ih2
      · exact HasType.tquery
    | elam ctx A B se ce _ ih =>
      simp [elabTyp]
      exact HasType.tlam ih
    | erproj ctx A B se ce l _ hlook ih =>
      exact HasType.trproj ih (type_safe_record_lookup hlook)
    | eclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>

      simp [elabTyp]
      exact HasType.tclos (sorry) ih1 ih2  -- need: Value ce1
    | elrec ctx A se ce l _ ih =>
      simp [elabTyp]
      exact HasType.trcd ih
    | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      sorry
    | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
      sorry
    | mstruct ctx ctxInner B sb se ce envCore hs1 hs2 _ ih =>
      simp [elabTyp, elabModTyp]
      cases sb with
      | sandboxed =>
        have := hs1 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tbox HasType.tunit ih
      | open_ =>
        have := hs2 rfl
        rw [this] at ih
        exact HasType.tbox HasType.tquery ih
    | mfunctor ctx ctxInner A B sb se ce hs1 hs2 _ ih =>
      simp [elabTyp, elabModTyp]
      cases sb with
      | sandboxed =>
        have := hs1 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tbox HasType.tunit (HasType.tlam ih)
      | open_ =>
        have := hs2 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tlam ih
    | mclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
      simp [elabTyp, elabModTyp]
      exact HasType.tclos (sorry) ih1 ih2  -- need: Value ce1
    | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      simp [elabTyp]
      exact HasType.tapp ih1 ih2
    | mlink ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      simp [elabTyp]
      sorry

-- ============================================
-- Values elaborate to values
-- ============================================



/--
  If es elaborates to ec, and es evaluates to vs under ρs,
  and ρs elaborates to ρc, then ec evaluates to some vc
  under ρc, and vs elaborates to vc.
-/
theorem semantic_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BStep ρs es vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs A vc := by sorry

/--
  A closed well-elaborated program evaluates
  consistently across source and core.
-/
theorem whole_program_correctness
    {A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp} {vs : SCE.Exp}
    (helab : elabExp SCE.Typ.top es A ec)
    (heval : S_Sem.BStep .unit es vs)
    : ∃ vc, EBig .unit ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  exact semantic_preservation helab heval (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

-- Linking and separate compilation

def linkSCE (e₁ e₂ : SCE.Exp) : SCE.Exp :=
  .mlink e₁ e₂

def linkCore (e₁ e₂ : Core.Exp) : Core.Exp :=
  .mrg e₁ (.app e₂ e₁)

/--
  Separate compilation: compiling components separately
  then linking in core preserves the behavior of
  linking in source then evaluating.
-/
theorem separate_compilation
    {Γ A : SCE.Typ} {mt : SCE.ModTyp}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ A ec₁)
    (helab₂ : elabExp Γ es₂ (SCE.Typ.sig (SCE.ModTyp.TyArrM A mt)) ec₂)
    (heval : S_Sem.BStep ρs (linkSCE es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc (linkCore ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and A (.sig mt)) vc := by
  have hmlink : elabExp Γ (linkSCE es₁ es₂) (.and A (.sig mt))
      (linkCore ec₁ ec₂) :=
    elabExp.mlink Γ A mt es₁ es₂ ec₁ ec₂ helab₁ helab₂
  exact semantic_preservation hmlink heval henv henv_val
