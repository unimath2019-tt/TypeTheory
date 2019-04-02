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
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
(* Require Import TypeTheory.ALV1.TypeCat. *)

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

        
        


