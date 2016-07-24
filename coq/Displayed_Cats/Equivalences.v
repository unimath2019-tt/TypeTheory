(**
“Displayed equivalences” of displayed (pre)categories
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require UniMath.Ktheory.Utilities.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Displayed_Cats.Auxiliary.
Require Import Systems.Displayed_Cats.Core.
Require Import Systems.Displayed_Cats.Constructions.


Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section Auxiliary.

Lemma invmap_eq {A B : UU} (f : A ≃ B) (b : B) (a : A)
  : b = f a → invmap f b = a.
Proof.
  intro H.
  apply (invmaponpathsweq f).
  etrans. apply homotweqinvweq. apply H.
Defined.  

End Auxiliary.

(* TODO: move somewhere.  Not sure where? [Constructions]? *)
Section Essential_Surjectivity.

Definition fibre_functor_ess_split_surj 
    {C C' : Precategory} {D} {D'}
    {F : functor C C'} (FF : functor_over F D D')
    (H : functor_over_ff FF)
    {X : functor_over_ess_split_surj FF}
    {Y : isofibration D}
    (x : C)
  : Π yy : D'[{F x}], Σ xx : D[{x}], 
                iso (fibre_functor FF _ xx) yy.
Proof.
  intro yy.
  set (XR := X _ yy).
  destruct XR as [c'' [i [xx' ii]]].
  set (YY := Y _ _ i xx').
  destruct YY as [ dd pe ].
  mkpair.
  - apply dd.
  - 
    (* now need functor_over_on_iso_disp *)
    set (XR := functor_over_on_iso_disp FF pe).
    set (XR' := iso_inv_from_iso_disp XR).
    (* now need composition of iso_disps *)
    apply  (invweq (iso_disp_iso_fibre _ _ _ _)).
    set (XRt := iso_disp_comp XR' ii).
    transparent assert (XH : 
           (iso_comp (iso_inv_from_iso (functor_on_iso F i))
             (functor_on_iso F i) = identity_iso _ )).
    { apply eq_iso. cbn. simpl. unfold precomp_with.
      etrans. apply maponpaths_2. apply id_right.
      etrans. eapply pathsinv0. apply functor_comp. 
      etrans. Focus 2. apply functor_id. 
      apply maponpaths. apply iso_after_iso_inv.
   } 
    set (XRT := transportf (fun r => iso_disp r (FF x dd) yy ) 
                           XH).
    apply XRT.
    assumption.
Defined.

End Essential_Surjectivity.



Section Adjunctions.

(** In general, one can define displayed equivalences/adjunctions over any equivalences/adjunctions between the bases (and probably more generally still).  For now we just give the case over a single base precategory — i.e. over an identity functor. 

We give the “bidirectional” version first, and then the “handed” versions afterwards, with enough coercions between the two to (hopefully) make it easy to work with both versions. *)

Definition adjunction_over_id_data {C} (D D' : disp_precat C) : UU
:= Σ (FF : functor_over (functor_identity _) D D')
     (GG : functor_over (functor_identity _) D' D),
     (nat_trans_over (nat_trans_id _) 
            (functor_over_identity _) (functor_over_composite FF GG))
   × (nat_trans_over (nat_trans_id _ )
            (functor_over_composite GG FF) (functor_over_identity _)).

(* TODO: consider naming of these access functions *)
Definition left_adj_over_id {C} {D D' : disp_precat C}
  (A : adjunction_over_id_data D D')
  : functor_over _ D D'
:= pr1 A.

Definition right_adj_over_id {C} {D D' : disp_precat C}
  (A : adjunction_over_id_data D D')
  : functor_over _ D' D
:= pr1 (pr2 A).

Definition unit_over_id {C} {D D' : disp_precat C}
  (A : adjunction_over_id_data D D')
:= pr1 (pr2 (pr2 A)).

Definition counit_over_id {C} {D D' : disp_precat C}
  (A : adjunction_over_id_data D D')
:= pr2 (pr2 (pr2 A)).

(** Triangle identies for an adjunction *)

(** TODO: currently the statements of these axioms include [_stmt_] to distinguish them from the _instances_ of these statements given by the access functions of [form_adjunction].  Does UniMath have an established naming convention for this distinction anywhere? *)

Definition triangle_1_stmt_over_id  {C} {D D' : disp_precat C}
    (A : adjunction_over_id_data D D')
    (FF := left_adj_over_id A)
    (η := unit_over_id A)
    (ε := counit_over_id A)
  : UU
:= Π x xx, #FF ( η x xx) ;;  ε _ (FF _ xx) 
            = transportb _ (id_left _ ) (id_disp _) .

Definition triangle_2_stmt_over_id  {C} {D D' : disp_precat C}
    (A : adjunction_over_id_data D D')
    (GG := right_adj_over_id A)
    (η := unit_over_id A)
    (ε := counit_over_id A)
  : UU
:= Π x xx, η _ (GG x xx) ;; # GG (ε _ xx)
           = transportb _ (id_left _ ) (id_disp _).

Definition form_adjunction_over_id {C} {D D' : disp_precat C}
    (A : adjunction_over_id_data D D')
  : UU
:= triangle_1_stmt_over_id A × triangle_2_stmt_over_id A.

Definition adjunction_over_id {C} (D D' : disp_precat C) : UU
:= Σ A : adjunction_over_id_data D D', form_adjunction_over_id A.

Definition data_of_adjunction_over_id {C} {D D' : disp_precat C}
  (A : adjunction_over_id D D')
:= pr1 A.
Coercion data_of_adjunction_over_id
  : adjunction_over_id >-> adjunction_over_id_data.

Definition triangle_1_over_id {C} {D D' : disp_precat C}
  (A : adjunction_over_id D D')
:= pr1 (pr2 A).

Definition triangle_2_over_id {C} {D D' : disp_precat C}
  (A : adjunction_over_id D D')
:= pr1 (pr2 A).

(** ** Left- and right- adjoints to a given functor *)

(** The terminology is difficult to choose here: the proposition “F is a left adjoint” is the same as this type of “right adjoints to F”, so should this type be called something more like [left_adjoint F] or [right_adjoint F]?

Our choice here does _not_ agree with that of the base UniMath category theory library. TODO: consider these conventions, and eventually harmonise them by changing it either here or in UniMath. *)

Definition right_adjoint_over_id_data {C} {D D' : disp_precat C}
  (FF : functor_over (functor_identity _) D D') : UU
:= Σ (GG : functor_over (functor_identity _) D' D),
     (nat_trans_over (nat_trans_id _) 
            (functor_over_identity _) (functor_over_composite FF GG))
   × (nat_trans_over (nat_trans_id _ )
            (functor_over_composite GG FF) (functor_over_identity _)).

Definition functor_of_right_adjoint_over_id {C} {D D' : disp_precat C}
  {FF : functor_over _ D D'}
  (GG : right_adjoint_over_id_data FF)
:= pr1 GG.
Coercion functor_of_right_adjoint_over_id
  : right_adjoint_over_id_data >-> functor_over.

Definition adjunction_of_right_adjoint_over_id_data {C} {D D' : disp_precat C}
    {FF : functor_over _ D D'}
    (GG : right_adjoint_over_id_data FF)
  : adjunction_over_id_data D D'
:= (FF,, GG). 
Coercion adjunction_of_right_adjoint_over_id_data
  : right_adjoint_over_id_data >-> adjunction_over_id_data.

Definition right_adjoint_over_id {C} {D D' : disp_precat C}
  (FF : functor_over (functor_identity _) D D') : UU
:= Σ GG : right_adjoint_over_id_data FF,
   form_adjunction_over_id GG.

Definition data_of_right_adjoint_over_id {C} {D D' : disp_precat C}
  {FF : functor_over _ D D'}
  (GG : right_adjoint_over_id FF)
:= pr1 GG.
Coercion data_of_right_adjoint_over_id
  : right_adjoint_over_id >-> right_adjoint_over_id_data.

Definition adjunction_of_right_adjoint_over_id {C} {D D' : disp_precat C}
    {FF : functor_over _ D D'}
    (GG : right_adjoint_over_id FF)
  : adjunction_over_id D D'
:= (adjunction_of_right_adjoint_over_id_data GG ,, pr2 GG). 
Coercion adjunction_of_right_adjoint_over_id
  : right_adjoint_over_id >-> adjunction_over_id.
(* Don’t worry about the ambiguous path generated here: the two ways round are equal. *)

(* TODO: add the dual-handedness version, i.e. indexed over GG instead of FF. *)
End Adjunctions.

Section Equivalences.
(** ** Equivalences (adjoint and quasi) *)
Definition form_equiv_over_id {C} {D D' : disp_precat C}
    (A : adjunction_over_id_data D D')
    (η := unit_over_id A)
    (ε := counit_over_id A)
  : UU
:= (Π x xx, is_iso_disp (identity_iso _ ) (η x xx)) 
 × (Π x xx, is_iso_disp (identity_iso _ ) (ε x xx)).

Definition is_iso_unit_over_id {C} {D D' : disp_precat C}
  {A : adjunction_over_id_data D D'}
  (E : form_equiv_over_id A)
:= pr1 E.

Definition is_iso_counit_over_id {C} {D D' : disp_precat C}
  {A : adjunction_over_id_data D D'}
  (E : form_equiv_over_id A)
:= pr2 E.

Definition equiv_over_id {C} (D D' : disp_precat C) : UU
:= Σ A : adjunction_over_id D D', form_equiv_over_id A.

Definition adjunction_of_equiv_over_id {C} {D D' : disp_precat C}
  (A : equiv_over_id D D')
:= pr1 A.
Coercion adjunction_of_equiv_over_id
  : equiv_over_id >-> adjunction_over_id.

Definition axioms_of_equiv_over_id {C} {D D' : disp_precat C}
  (A : equiv_over_id D D')
:= pr2 A.
Coercion axioms_of_equiv_over_id
  : equiv_over_id >-> form_equiv_over_id.

Definition is_equiv_over_id {C} {D D' : disp_precat C}
  (FF : functor_over (functor_identity _) D D') : UU
:= Σ GG : right_adjoint_over_id FF,
   form_equiv_over_id GG.

Definition right_adjoint_of_is_equiv_over_id {C} {D D' : disp_precat C}
  {FF : functor_over _ D D'}
  (GG : is_equiv_over_id FF)
:= pr1 GG.
Coercion right_adjoint_of_is_equiv_over_id
  : is_equiv_over_id >-> right_adjoint_over_id.

Definition equiv_of_is_equiv_over_id {C} {D D' : disp_precat C}
    {FF : functor_over _ D D'}
    (GG : is_equiv_over_id FF)
  : equiv_over_id D D'
:= (adjunction_of_right_adjoint_over_id GG ,, pr2 GG). 
Coercion equiv_of_is_equiv_over_id
  : is_equiv_over_id >-> equiv_over_id.
(* Again, don’t worry about the ambiguous path generated here. *)

(* TODO: right-handed versions *)

(* TODO: [quasi_equiv_over_id] (without triangle identities). *)

(** ** Lemmas on the triangle identities *)

(* TODO: search in library!  I’m sure I’ve seen it there before, but can’t find it now. If not: upstream. *)
Lemma transportb_transpose {X : UU} {P : X → UU}
  {x x' : X} (e : x = x') (y : P x) (y' : P x')
: transportf P e y = y' -> y = transportb P e y'.
Proof.
  destruct e; auto.
Defined.

Lemma transportf_transpose {X : UU} {P : X → UU}
  {x x' : X} (e : x = x') (y : P x) (y' : P x')
: transportb P e y' = y -> y' = transportf P e y.
Proof.
  destruct e; auto.
Defined.

(* TODO: move these two lemmas, and this documentation lone, to CORE.*)
(** All the axioms are given in two versions, with the transport on different sides, so that they can be invoked easily when either side is known. *) 
Lemma id_left_disp_var {C} {D : disp_precat C} 
  {x y} {f : x ⇒ y} {xx : D x} {yy} {ff : xx ⇒[f] yy}
: ff = transportf _ (id_left _) (id_disp _ ;; ff).
Proof.
  apply transportf_transpose.
  apply @pathsinv0, id_left_disp.
Qed.

Definition id_right_disp_var {C} {D : disp_precat C} 
  {x y} {f : x ⇒ y} {xx : D x} {yy} {ff : xx ⇒[f] yy}
  : ff = transportf _ (id_right _) (ff ;; id_disp _).
Proof.
  apply transportf_transpose.
  apply @pathsinv0, id_right_disp.
Qed.

(* A useful notation for hiding the huge irrelevant equalities that occur in algebra of displayed categories.

TODO: move and document! 

Level is chosen to bind *tighter* than categorical composition. *)
Notation "?# x" := (transportf _ _ x) (at level 45) : short_transport.
Notation "?#' x" := (transportb _ _ x) (at level 45) : short_transport.
Delimit Scope short_transport with short.
Local Open Scope short_transport.

Lemma triangle_2_from_1_for_equiv_over_id
  {C} {D D' : disp_precat C}
  (A : adjunction_over_id_data D D')
  (E : form_equiv_over_id A)
: triangle_1_stmt_over_id A -> triangle_2_stmt_over_id A.
Proof.
  destruct A as [FF [GG [η ε]]].
  destruct E as [Hη Hε]; cbn in Hη, Hε.
  unfold triangle_1_stmt_over_id, triangle_2_stmt_over_id; cbn.
  intros T1 x yy.
  (* Algebraically, this goes as follows:
  η G ; G ε
  = G ε^ ; η^ G ; η G ; G ε ; η G ; G ε          [by inverses, 1]
  = G ε^ ; η^ G ; η G ; η G F G ; G F G ε ; G ε  [by naturality, 2]
  = G ε^ ; η^ G ; η G ; η G F G ; G ε F G ; G ε  [by naturality, 3]
  = G ε^ ; η^ G ; η G ; G F η G ; G ε F G ; G ε  [by naturality, 4]
  = G ε^ ; η^ G ; η G ; G (F η ; ε F ) G ; G ε   [by functoriality, 5]
  = G ε^ ; η^ G ; η G ; G ε                      [by T1, 6]
  = 1                                            [by inverses, 7]

  It’s very readable when written with string diagrams. *)
  etrans. apply id_left_disp_var.
  etrans. apply maponpaths.
    etrans. apply maponpaths_2.
      etrans. eapply transportb_transpose. apply @pathsinv0.
        refine (iso_disp_after_inv_mor _).
        refine (functor_over_on_is_iso_disp GG _).
        apply Hε. (*1a*)
      etrans. apply maponpaths, maponpaths_2.
        etrans. apply id_right_disp_var.
        etrans. apply maponpaths.
          etrans. apply maponpaths.
            eapply transportb_transpose. apply @pathsinv0.
            refine (iso_disp_after_inv_mor _).
            apply (Hη). (*1b*)
          etrans. apply mor_disp_transportf_prewhisker.
          etrans. apply maponpaths, assoc_disp.
          apply transport_f_f.
        apply transport_f_f.
      etrans. apply maponpaths, mor_disp_transportf_postwhisker.
      apply transport_f_f.
    apply mor_disp_transportf_postwhisker. 
  etrans. apply transport_f_f.
  etrans. apply maponpaths.
    etrans. apply assoc_disp_var.
    etrans. apply maponpaths.
      etrans. apply assoc_disp_var.
      etrans. apply maponpaths.
        etrans. apply maponpaths.
          etrans. apply maponpaths.
            etrans. apply assoc_disp.
            etrans. apply maponpaths.
              etrans. apply maponpaths_2.
                refine (nat_trans_over_ax η (# GG (ε x yy))). (*2*)
              etrans. apply mor_disp_transportf_postwhisker.
              etrans. apply maponpaths.
                etrans. apply assoc_disp_var.
                etrans. apply maponpaths.
                  etrans. apply maponpaths.
                    cbn.
                    etrans. eapply transportf_transpose.
                      apply @pathsinv0, (functor_over_comp GG).
                    etrans. apply maponpaths, maponpaths.
                      apply (nat_trans_over_ax ε). (*3*)
                    cbn. unfold idfun.
                    etrans. apply (functor_over_transportf _ GG).
                    etrans. apply maponpaths.
                      apply functor_over_comp.
                    apply transport_f_f.
                  cbn. apply mor_disp_transportf_prewhisker.
                apply transport_f_f.
              apply transport_f_f.
            apply transport_f_f.
          etrans. apply mor_disp_transportf_prewhisker.
          etrans. apply maponpaths.
            etrans. apply assoc_disp.
            etrans. apply maponpaths.
              etrans. apply maponpaths_2.
                apply (nat_trans_over_ax η (η x (GG x yy))). (*4*)
              cbn. apply mor_disp_transportf_postwhisker.
            etrans. apply transport_f_f.
            etrans. apply maponpaths.
              etrans. apply assoc_disp_var.
              etrans. apply maponpaths.
                etrans. apply maponpaths.
                  etrans. apply assoc_disp.
                  etrans. apply maponpaths.
                    etrans. apply maponpaths_2.
                      etrans. eapply transportf_transpose.
                        apply @pathsinv0, (functor_over_comp GG). (*5*)
                      etrans. apply maponpaths.
                        etrans. apply maponpaths.
                          apply T1. (*6*)
                        etrans. apply (functor_over_transportf _ GG).
                        etrans. apply maponpaths, functor_over_id.
                        apply transport_f_f.
                      apply transport_f_f.
                    etrans. apply mor_disp_transportf_postwhisker.
                    etrans. apply maponpaths.
                      apply id_left_disp.
                    apply transport_f_f.
                  apply transport_f_f.
                apply mor_disp_transportf_prewhisker.
              apply transport_f_f.
            apply transport_f_f.
          apply transport_f_f.
        etrans. apply mor_disp_transportf_prewhisker.
        etrans. apply maponpaths.
          etrans. apply assoc_disp_var.
          etrans. apply maponpaths.
            etrans. apply maponpaths.
              etrans. apply assoc_disp.
              etrans. apply maponpaths.
                etrans. apply maponpaths_2.
                  refine (iso_disp_after_inv_mor _). (*7a*)
                etrans. apply mor_disp_transportf_postwhisker.
                etrans. apply maponpaths.
                  apply id_left_disp.
                apply transport_f_f.
              apply transport_f_f.
            etrans. apply mor_disp_transportf_prewhisker.
            etrans. apply maponpaths.
              refine (iso_disp_after_inv_mor _). (*7b*)
            apply transport_f_f.
          apply transport_f_f.
        apply transport_f_f.
      apply transport_f_f.
    apply transport_f_f.
  etrans. apply transport_f_f.
  unfold transportb. apply maponpaths_2, homset_property.
(* Time Qed. *)
Admitted.
(* TODO: [Qed.] takes about 30sec!  Try to find some lemmas to simplify this + speed it up.

TODO: implement the following lemmas, and see how they help above (and elsewhere).
Some particularly recurring patterns (using the ?# notation for transport):

Goal: [ ?# (T1) = ? ]
  etrans. maponpaths.
    (long proof of [ T1 = ?# T2 ]).
  apply transport_f_f.

So make this as:

Lemma that [ T1 = ?# T2 -> ?# T1 = ?# T2 ].  Hah: it’s like Klesli bind of a monad in Haskell…  What to call this?  [transportf_bind]?

Two more common patterns: the mor_disp versions of cancel_precomposition and cancel_postcomposition, which go like

Goal: [ T1 ;; T2 = ? ]
  etrans. maponpaths_2.
    (proof of [ T1 = ?# T1'])
  apply mor_disp_transportf_postwhisker.

or else

  etrans. maponpaths.
    (proof of [ T2 = ?# T2'])
  apply mor_disp_transportf_prewhisker.

So: lemmas
[cancel_precomposition_disp : T1 = ?# T2' -> T1 ;; T2 = ?# (T1 ;; T2') ]
and dually [cancel_precomposition_disp].
 *)

Lemma triangle_1_from_2_for_equiv_over_id
  {C} {D D' : disp_precat C}
  (A : adjunction_over_id_data D D')
  (E : form_equiv_over_id A)
: triangle_2_stmt_over_id A -> triangle_1_stmt_over_id A.
Proof.
  (* dual to previous lemma *)
Admitted.

(* TODO: adjointification of a quasi-equivalence. *)

End Equivalences.

(** * Full + faithful + ess split => equivalence *)
Section Equiv_from_ff_plus_ess_split.

Context {C : Precategory} {D' D : disp_precat C}
        (FF : functor_over (functor_identity _) D' D)
        (FF_split : functor_over_disp_ess_split_surj FF)
        (FF_ff : functor_over_ff FF).

(** ** Utility lemmas from fullness+faithfulness *)
 
Let FFweq {x y} {xx yy} f := weqpair _ (FF_ff x y xx yy f).
Let FFinv {x y} {xx yy} f := invmap (@FFweq x y xx yy f).

Lemma FFinv_identity {x : C} (xx : D' x)
  : FFinv (identity _) (id_disp (FF _ xx))
  = id_disp xx.
Proof.
  apply invmap_eq. cbn.
  apply pathsinv0. 
  apply (functor_over_id FF).
Qed.

Lemma FFinv_compose (x y z : C) (f : x ⇒ y) (g : y ⇒ z)
    (xx : D' x) (yy : D' y) (zz : D' z) 
    (ff : FF _ xx ⇒[f] FF _ yy) (gg : FF _ yy ⇒[g] FF _ zz)
  : FFinv (f ;; g) (ff ;; gg) = FFinv f ff ;; FFinv _ gg.
Proof.
  apply invmap_eq. cbn.
  apply pathsinv0.
  etrans. apply (functor_over_comp FF).
  cbn; unfold idfun. etrans.
  - apply maponpaths, (homotweqinvweq (FFweq _ )).
  - apply maponpaths_2, (homotweqinvweq (FFweq _ )).
Qed.

Lemma FFinv_transportf
    {x y : C} {f f' : x ⇒ y} (e : f = f')
    {xx : D' x} {yy : D' y} (ff : FF _ xx ⇒[f] FF _ yy)
  : FFinv _ (transportf _ e ff) = transportf _ e (FFinv _ ff).
Proof.
  induction e.
  apply idpath.
Qed.

(** ** Converse functor *)

Local Definition GG_data : functor_over_data (functor_identity _ ) D D'.
Proof.
  mkpair.
  + intros x xx. exact (pr1 (FF_split x xx)).
  + intros x y xx yy f ff; simpl.
    set (Hxx := FF_split x xx).
    set (Hyy := FF_split y yy).
    apply FFinv.
    refine (transportf (mor_disp _ _) _ _). Focus 2.
    exact ((pr2 Hxx ;; ff) ;; inv_mor_disp_from_iso (pr2 Hyy)).
    cbn. etrans. apply id_right. apply id_left.
Defined.

Local Lemma GG_ax : functor_over_axioms GG_data.
Proof.
  split; simpl.
  + intros x xx.
    apply invmap_eq. cbn.
    etrans. Focus 2. apply @pathsinv0, (functor_over_id FF).
    etrans. apply maponpaths.
      etrans. apply maponpaths_2, id_right_disp.
      etrans. apply mor_disp_transportf_postwhisker.
      apply maponpaths, (inv_mor_after_iso_disp (pr2 (FF_split _ _))).
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    unfold transportb. apply maponpaths_2, homset_property.
  + intros x y z xx yy zz f g ff gg.
    apply invmap_eq. cbn.
    etrans. Focus 2. apply @pathsinv0.
      etrans. apply (functor_over_comp FF).
      etrans. apply maponpaths.
        etrans. apply maponpaths, (homotweqinvweq (FFweq _ )).
        apply maponpaths_2, (homotweqinvweq (FFweq _ )).
      etrans. apply maponpaths.
        etrans. apply mor_disp_transportf_prewhisker.
        apply maponpaths.
        etrans. apply mor_disp_transportf_postwhisker.
        apply maponpaths.
        etrans. apply maponpaths, assoc_disp_var.
        etrans. apply mor_disp_transportf_prewhisker.
        apply maponpaths.
        etrans. apply assoc_disp.
        apply maponpaths.
        etrans. apply maponpaths_2.
          etrans. apply assoc_disp_var.
          apply maponpaths.
          etrans. apply maponpaths.
            refine (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
          etrans. apply mor_disp_transportf_prewhisker.
          etrans. apply maponpaths, id_right_disp.
          apply transport_f_f.
        etrans. apply maponpaths_2, transport_f_f.
        apply mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      (* A trick to hide the huge equality term: *)
      apply maponpaths_2. shelve.
    etrans. apply maponpaths.
      etrans. apply maponpaths_2, assoc_disp.
      etrans. apply mor_disp_transportf_postwhisker.
      apply maponpaths. apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    apply maponpaths_2, homset_property.
    Unshelve. Focus 2. apply idpath.
Qed.

Definition GG : functor_over _ _ _ := (_ ,, GG_ax).


(* Alternate typing for ε, using the displayed functor category:

     (functor_over_composite GG FF : (disp_functor_precat _ _ D D) _ ) 
    ⇒[ @identity_iso (functor_precategory C C (homset_property C)) _ ] 
     functor_over_identity _ 

*)

Definition ε_ses_ff_data
  : nat_trans_over_data (nat_trans_id _ )
      (functor_over_composite GG FF) (functor_over_identity _ )
:= fun x xx => (pr2 (FF_split x xx)).

Lemma ε_ses_ff_ax : nat_trans_over_axioms ε_ses_ff_data.
Proof.
  intros x y f xx yy ff. cbn. unfold ε_ses_ff_data.
  etrans. apply maponpaths_2, (homotweqinvweq (FFweq _ )).
  etrans. apply mor_disp_transportf_postwhisker.
  etrans. apply maponpaths.
    etrans. apply assoc_disp_var.
    apply maponpaths.
    etrans. apply maponpaths.
      apply (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
    etrans. apply mor_disp_transportf_prewhisker.
    apply maponpaths, id_right_disp.
  etrans. apply transport_f_f.
  etrans. apply transport_f_f.
  etrans. apply transport_f_f.
  unfold transportb. apply maponpaths_2, homset_property.
Qed.

Definition ε_ses_ff
  : nat_trans_over (nat_trans_id _ )
      (functor_over_composite GG FF) (functor_over_identity _ )
:= (ε_ses_ff_data,, ε_ses_ff_ax).

Definition η_ses_ff_data
  : nat_trans_over_data (nat_trans_id _)
      (functor_over_identity _ ) (functor_over_composite FF GG).
Proof.
  intros x xx. cbn.
  apply FFinv.
  refine (inv_mor_disp_from_iso (pr2 (FF_split _ _))).
Defined.

Definition η_ses_ff_ax
  : nat_trans_over_axioms η_ses_ff_data.
Proof.
  intros x y f xx yy ff. cbn. unfold η_ses_ff_data.
  (* This feels a bit roundabout.  Can it be simplified? *)
  apply @pathsinv0.
  etrans. apply maponpaths.
    etrans. apply @pathsinv0, FFinv_compose.
    apply maponpaths.
    etrans. apply mor_disp_transportf_prewhisker.
    apply maponpaths.
    etrans. apply assoc_disp.
    apply maponpaths.
    etrans. apply maponpaths_2. 
      etrans. apply assoc_disp.
      apply maponpaths. 
      etrans.
        apply maponpaths_2, (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths, id_left_disp.
      apply transport_f_f.
    etrans. apply maponpaths_2, transport_f_f. 
    apply mor_disp_transportf_postwhisker.
  etrans. apply maponpaths.
    etrans. apply maponpaths. 
      etrans. apply transport_f_f.
      apply transport_f_f.
    apply FFinv_transportf.
  etrans. apply transport_f_f.
  apply transportf_comp_lemma_hset.
    apply homset_property.
  etrans. apply FFinv_compose.
  apply maponpaths_2, homotinvweqweq.
Qed.

Definition η_ses_ff
  : nat_trans_over (nat_trans_id _)
      (functor_over_identity _ ) (functor_over_composite FF GG)
:= (_ ,, η_ses_ff_ax).

Definition GGεη : right_adjoint_over_id_data FF
  := (GG,, (η_ses_ff,, ε_ses_ff)).

Lemma form_equiv_GGεη : form_equiv_over_id GGεη.
Proof.
  split; intros x xx; cbn.
  - unfold η_ses_ff_data.
    (* TODO: FFinv preserves isos; or, roughly equivalently, ff functors reflect isos.  Then use that plus [is_iso_disp_from_iso]. *)
     admit.
  - unfold ε_ses_ff_data.
    apply is_iso_disp_from_iso.
Admitted.

Lemma tri_1_GGεη : triangle_1_stmt_over_id GGεη.
Proof.
  (* TODO: complete this. *)
Admitted.

Lemma tri_2_GGεη : triangle_2_stmt_over_id GGεη.
Proof.
  apply triangle_2_from_1_for_equiv_over_id.
  apply form_equiv_GGεη.
  apply tri_1_GGεη.
Qed.

Theorem is_equiv_from_ff_ess_over_id : is_equiv_over_id FF.
Proof.
  simple refine ((GGεη,, _) ,, _).
  split. apply tri_1_GGεη. apply tri_2_GGεη.
  apply form_equiv_GGεη.
Defined.

End Equiv_from_ff_plus_ess_split.

Section Displayed_Equiv_Compose.

(* TODO: give composites of displayed equivalences. *)

End Displayed_Equiv_Compose.

Section Equiv_Fibres.

(* TODO: move *)
Definition fibre_nat_trans {C C' : Precategory}
  {F : functor C C'}
  {D D'} {FF FF' : functor_over F D D'}
  (α : nat_trans_over (nat_trans_id F) FF FF')
  (c : C)
: nat_trans (fibre_functor FF c) (fibre_functor FF' c).
Proof.
  use tpair; simpl.
  - intro d. exact (α c d).
  - unfold is_nat_trans; intros d d' ff; simpl.
    set (αff := pr2 α _ _ _ _ _ ff); simpl in αff.
    cbn.
    etrans. apply maponpaths, mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, αff.
    etrans. apply transport_f_b.
    apply @pathsinv0.
    etrans. apply maponpaths, mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    apply maponpaths_2, homset_property.
Defined.

(* TODO: move *)
Definition is_iso_fibre_from_is_iso_disp
  {C : Precategory} {D : disp_precat C}
  {c : C} {d d' : D c} (ff : d ⇒[identity c] d')
  (Hff : is_iso_disp (identity_iso c) ff)
: @is_iso (fibre_precategory D c) _ _ ff.
Proof.
  apply is_iso_from_is_z_iso.
  exists (pr1 Hff).
  mkpair; cbn.
  + set (H := pr2 (pr2 Hff)).
    etrans. apply maponpaths, H.
    etrans. apply transport_f_b.
    (* TODO: the following slightly cumbersome step is used in several spots.  Is there a lemma for it?  If not, make one? *)
(*    apply transportf_comp_lemma_hset. 
      is a lemma crafted by PLL that might be applied here; 
      a variant with only [x] would be useful
                    *)
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.      
  + set (H := pr1 (pr2 Hff)).
    etrans. apply maponpaths, H.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
Qed.

Context {C : Precategory}.

Definition fibre_is_left_adj {D D' : disp_precat C}
  {FF : functor_over (functor_identity _) D D'}
  (EFF : right_adjoint_over_id FF)
  (c : C)
: is_left_adjoint (fibre_functor FF c).
Proof.
  destruct EFF as [[GG [η ε]] axs]; simpl in axs.
  exists (fibre_functor GG _).
  exists (fibre_nat_trans η _,
          fibre_nat_trans ε _).
  mkpair; cbn.
  + intros d.
    set (thisax := pr1 axs c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
  + intros d.
    set (thisax := pr2 axs c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
Defined.

Definition fibre_equiv {D D' : disp_precat C}
  {FF : functor_over (functor_identity _) D D'}
  (EFF : is_equiv_over_id FF)
  (c : C)
: adj_equivalence_of_precats (fibre_functor FF c).
Proof.
  exists (fibre_is_left_adj EFF c).
  destruct EFF as [[[GG [η ε]] tris] isos]; cbn in isos; cbn.
  mkpair.
  + intros d.
    apply is_iso_fibre_from_is_iso_disp. 
    apply (is_iso_unit_over_id isos).
  + intros d.
    apply is_iso_fibre_from_is_iso_disp. 
    apply (is_iso_counit_over_id isos).
Defined.

End Equiv_Fibres.

(* *)





