Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.

Local Open Scope cat.

Section sets.


Definition pre_guniverse : UU := ∑ (A : hSet), A → hSet.
Definition pr1GUni : pre_guniverse -> hSet := @pr1 hSet _.
Coercion pr1GUni: pre_guniverse >-> hSet.
Definition El {A : pre_guniverse} : A → hSet := (pr2 A).

Theorem emptyisaset : isaset empty.
Proof. intros a. contradiction. Defined.
Definition emptyset : hSet := hSetpair empty emptyisaset.

Definition guniverse_sigma (A : pre_guniverse) : UU :=
  ∏ (a : A) (b : El a → A),
    ∑ (p : A), El p  = (∑ (x : El a), El (b x))%set.

Axiom V : pre_guniverse.
Axiom Vsigma : guniverse_sigma V.


Definition VSET : precategory.
  use tpair; cbn.
  - use tpair.
    + use tpair.
      * exact V.
      * cbn.
        exact (λ a b, El a → El b).
    + use tpair; cbn.
      * exact (λ _ a, a).
      * exact (λ _ _ _ f g x, g (f x)). 
  - repeat use tpair; cbn; intros; reflexivity.
Defined.

(*Definition VSET_tt_structure : tt_structure VSET.
Proof.
use tpair.  
- intro Γ.
  exact (∑ (E : V), El E -> El Γ).
- simpl.
  intros Γ A.
  exact (∑ t : El Γ -> El (pr1 A), forall x, (pr2 A) (t x) = x).
Defined.
*)

Definition VSET_tt_structure : tt_structure VSET.
Proof.
use tpair.  
- intro Γ.
  exact (El Γ -> V).
- simpl.
  intros Γ A.
  exact (∏ c : El Γ, El (A c)).
Defined.
  
Lemma VSET_reindx_structure : reindx_structure VSET_tt_structure.
Proof.
  use tpair.
  - cbn.
    intros Δ Γ A σ c.
    exact (A (σ c)).
  - cbn.
    intros Δ Γ A a σ d.
    exact (a (σ d)).
Defined.
    
Definition VSET_tt_reindx_type_struct : tt_reindx_type_struct VSET.
Proof.
  unfold tt_reindx_type_struct, tt_reindx_comp_1_struct, comp_2_struct.
  use tpair.
  - unfold  tt_reindx_struct.
    use tpair.
    + exact (VSET_tt_structure,, VSET_reindx_structure).
    + cbn.
      unfold comp_1_struct.
      cbn.
      intros Γ A.
      destruct (Vsigma _ A) as [ΓA e].
      exists ΓA.
      SearchAbout (?x = ?y -> ?y = ?x).
      apply (@transportf _ (fun z => z →  El Γ) _ _ (pathsinv0 (base_paths _ _ e))).
      exact pr1.
  - simpl.
    intros Γ A.
    cbn.
    split;
    destruct (Vsigma Γ A) as [ΓA e]; cbn; unfold pr1hSet in *.
    + apply transportD.
        exact pr2.
    + intros.
       apply (@transportf _ (fun z => z) _ _ (! (base_paths _ _ e))).
       cbn in *. 
       exists (γ X).
       apply a.        
Defined.

       
Lemma VSET_reindx_laws : reindx_laws VSET_tt_reindx_type_struct.
Proof.
  unfold reindx_laws.
  use tpair.
  - unfold reindx_laws_type.
    simpl.
    split.
    + intros Γ A.
      cbn.
      exact (idpath A).
    + intros.
      exact (idpath _).
  - simpl.
    unfold reindx_laws_terms.
    simpl.
    use tpair.
    + intros.
      exact (idpath _).
    + simpl.
      intros.
      exact (idpath _).
 Defined.


Definition VSET_CwF : cwf_struct (VSET).
Proof.
  exists VSET_tt_reindx_type_struct.
  unfold cwf_laws.
  simpl.
  Print cwf_laws.
  use tpair.
  - exists VSET_reindx_laws.
    unfold comp_laws_1_2.
    simpl.
    use tpair.
    + intros.
      unfold pairing.
      simpl.
      use tpair.
      * unfold compose.
        apply funextfun; intros x;  cbn.
        Check @transportD.
         destruct (Vsigma Γ A) as [ΓA e]; cbn.
         fold pr1hSet in *.
        admit.
      * simpl.
         admit.
   + simpl.
      unfold comp_law_3.
      simpl.
      use tpair.
      * unfold compose.
        simpl.
        intros.
        exact (idpath _).
      * simpl.
        unfold comp_law_4.
        admit.
  - simpl.
    use tpair.
    * unfold has_homsets.
      intros.
      simpl.
      unfold hset_precategory_ob_mor in *.
      apply isaset_set_fun_space.
    * simpl.
      use tpair.
      + admit.
      + simpl.
        intros.
        apply isaset_forall_hSet.
Admitted.

        
        


