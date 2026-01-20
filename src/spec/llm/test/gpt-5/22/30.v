Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Definition Any := list R.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Axiom NonInt_list : forall n, ~ IsInt [2.7%R; 3.0%R; 1.5%R; 1.5%R] n.

Example test_case_floats: filter_integers_spec [[2.7%R; 3.0%R; 1.5%R; 1.5%R]] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - intros n. apply NonInt_list.
  - constructor.
Qed.