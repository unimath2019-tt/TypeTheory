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
    + simpl.
      unfold comp_1_struct.
      simpl.
      intros Γ A.
      use tpair.
      * exact (pr1 (Vsigma _ A)).
      * cbn.
        rewrite (pr2 (Vsigma _ A)); exact pr1.
  - simpl.
    intros Γ A.
    cbn.
    split.
    + destruct (Vsigma Γ A) as [C e]; cbn.
      intros.
      admit.
    + intros Δ σ a d.
      rewrite (pr2 (Vsigma Γ A)).
      exact (σ d,, a d).
Admitted.    

Lemma VSET_reindx_laws : reindx_laws VSET_tt_reindx_type_struct.
Proof.
Admitted.


Definition VSET_CwF : cwf_struct (VSET).
Proof.

Admitted.

        
        


