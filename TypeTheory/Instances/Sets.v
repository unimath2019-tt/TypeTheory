(**

This files proves that HSET (almost) forms a type category ([HSET_TypeCat]). As the
collection of types in context Γ don't form an hset it is not possible
to instantiate the CwF structure, however all of the other axioms of a
CwF have been formalized.

Contexts, written Γ ⊢, are modelled as HSETs and substitutions
are modelled by maps σ : Δ → Γ. So the identity
substitution is given by the identity map 1 : Γ → Γ
and composition of substitutions are given by composition of maps
σ · δ (note that the order is diagrammatic). So we
automatically get the equations:

<<
      1 · σ = σ · 1 = σ        (σ · δ) · τ = σ · (δ · τ)
>>

Types in context Γ, usually written Γ ⊢ A and written A : Γ ⊢ in the
formalization, are defined as families of HSETs over Γ. 
So A : Γ ⊢ means A : Γ -> HSET.

Terms a of type A in context Γ, usually written Γ ⊢ a : A and written
a : Γ ⊢ A in the formalization, are defined as sections of A. 

This is equivalent to sections s : Γ → Γ.A of the
projection map p : Γ.A → Γ (see [TermIn_to_TermInSection],
[TermInSection_to_TermIn]).

The operations then defined are:

<<
              Γ ⊢ A    σ : Δ → Γ
            ---------------------- ([subst_type])
                   Δ ⊢ Aσ


             Γ ⊢ a : A    σ : Δ → Γ
           -------------------------- ([subst_term)]
                 Δ ⊢ aσ : Aσ


                    Γ ⊢ A

                 ----------- ([ctx_ext])
                   Γ ⋆ A ⊢


                    Γ ⊢ A
               ----------------- ([ctx_proj])
                 p : Γ ⋆ A → Γ


                    Γ ⊢ A
              ------------------ ([ctx_last])
                Γ ⋆ A ⊢ q : Ap


             σ : Δ → Γ   Γ ⊢ A   Δ ⊢ a : Aσ
          ----------------------------------- ([subst_pair])
                (σ,a) : Δ → Γ ⋆ A


                  σ : Δ → Γ    Δ ⊢ A
                ---------------------- ([p_gen])
                  p_gen : Δ ⋆ A → Γ


                  σ : Δ → Γ    Γ ⊢ A
             ----------------------------- ([q_gen])
               Δ ⋆ Aσ ⊢ q_gen : A(p_gen)
>>

These satisfy the following equations:

<<
                       A1 = A            ([subst_type_id])

                    (Aσ)δ = A(σδ)        ([subst_type_comp])

                       a1 = a            ([subst_term_id])

                    (aσ)δ = a(σδ)        ([subst_term_comp])

                δ · (σ,a) = (δ · σ,aδ)   ([subst_pair_subst])

                (σ,a) · p = σ            ([subst_pair_p])

                   q(σ,a) = a            ([subst_pair_q])

                    (p,q) = 1            ([subst_pair_id])

        (p_gen,q_gen) · p = p · σ        ([q_gen_mor_p])
>>

And the last square is a pullback square ([isPullback_q_gen_mor]).

Written by: Anders Mörtberg, 2017

 *)
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Univalence.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

Local Open Scope cat.

Section sets.


Definition SET_tt_structure : tt_structure SET.
Proof.
use tpair.  
- intro Γ.
  exact (pr1 Γ → SET).
- simpl.
  intros Γ A.
  exact (∏ (c : Γ), A c).
Defined.

  
Lemma SET_reindx_structure : reindx_structure SET_tt_structure.
Proof.
  use tpair.
  - cbn.
    intros Δ Γ A σ c.
    exact (A (σ c)).
  - cbn.
    intros Δ Γ A a σ d.
    exact (a (σ d)).
Defined.

Definition SET_tt_reindx_type_struct : tt_reindx_type_struct SET.
Proof.
  unfold tt_reindx_type_struct, tt_reindx_comp_1_struct, comp_2_struct.
  use tpair.
  - unfold  tt_reindx_struct.
    use tpair.
    + exact (SET_tt_structure,, SET_reindx_structure).
    + simpl.
      unfold comp_1_struct.
      simpl.
      intros Γ A.
      use tpair.
      * exact (total2_hSet A).
      * simpl.
        exact pr1.
  - simpl.
    intros Γ A.
    cbn.
    split.
    + exact pr2.
    + intros Δ σ a d.
      exact (σ d,, a d).
Defined.
    
Lemma SET_reindx_laws : reindx_laws SET_tt_reindx_type_struct.
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

Axiom K : forall A : UU, isaset(A).

Definition SET_CwF : cwf_struct (SET).
Proof.
  exists SET_tt_reindx_type_struct.
  unfold cwf_laws.
  simpl.
  Print cwf_laws.
  use tpair.
  - exists SET_reindx_laws.
    unfold comp_laws_1_2.
    simpl.
    use tpair.
    + intros.
      unfold pairing.
      simpl.
      use tpair.
      * unfold compose.
        simpl.
        exact (idpath _).
      * simpl.
        exact (idpath _).
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
        intros.
        exact (idpath _).
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

(* Definition p_gen {Γ Δ : SET} {A : Δ } (σ : Δ --> Γ) : Δ ⋆ A --> Γ.  *)  

Section TypeCat.

Local Notation "Γ ⊢" := (pr1 Γ → SET) (at level 50).
Local Notation "Γ ⊢ A" :=  (∏ (c : Γ), A c) (at level 50).
Local Notation "A ⦃ s ⦄" := (λ c, A (s c)) (at level 40, format "A ⦃ s ⦄"). 
Local Notation "Γ ⋆ A" := (@total2_hSet Γ A) (at level 30).

Definition SET_TypeCat : typecat_structure SET.
Proof.
  unfold typecat_structure.
  use tpair.
  - unfold typecat_structure1.
    exists (λ Γ, Γ ⊢).
    exists (λ Γ A, Γ ⋆ A).
    intros Γ A Δ σ.
    exact (A⦃σ⦄).
  - cbn.
    unfold typecat_structure2.
    cbn.
    use tpair.
    + intros Γ A.
      exact pr1.
    + cbn.
      use tpair.
      * intros Γ A Δ σ (x,e).
        exact (σ x,, e).
      * cbn.
        use tpair.
        ** intros Γ A Δ σ.
           exact (idpath _).
        ** cbn.
           intros Γ A Δ σ.
           unfold isPullback.
           cbn.
           Locate "⦃".
           intros e h k p. 
           use tpair.
        ++ use tpair.
           intro z.
           use tpair.
           -- apply (h z).
           --  simpl.
             set (foo := pr2 (k z)).
             simpl in *.
             change (σ (h z)) with (σ⦃h⦄ z).
             exact ( transportf (λ f, A (f z)) (! p) foo ).
           -- simpl.
              use tpair.
              exact (idpath _).
              simpl.
              apply funextfun.
              intro x.
              change (σ (h x)) with (σ⦃h⦄ x).
              induction (!p).
              exact (idpath _).
              ++ cbn.
                 intros.
                 destruct t as [g [p1 p2]].
                 induction p1.
                 unshelve eapply (total2_paths_f).
                 +++ cbn.
                     apply funextfun.
                     intro y.
                     unshelve eapply (total2_paths_f).
                     cbn.
                     exact (idpath _).
                     cbn.
                     unfold idfun.
                     induction p2.
                     cbn.
                     assert (idpath _ = p).
                     admit. (*This is easy, because they're hsets *)                    
                     induction X.
                     reflexivity.
                 +++ admit. (*This is easy, because they're hsets *)
                 
         Admitted.
                         
End TypeCat.

