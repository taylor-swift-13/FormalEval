Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.

Parameter Any : Type.
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

Parameter injR : R -> Any.
Axiom injR_nonint : forall r n, ~ IsInt (injR r) n.

Example test_case_floats: filter_integers_spec [injR 1.5%R; injR 2.7%R; injR 3.0%R; injR 1.5%R] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - intro n. exact (injR_nonint 1.5%R n).
  - eapply fir_cons_nonint.
    + intro n. exact (injR_nonint 2.7%R n).
    + eapply fir_cons_nonint.
      * intro n. exact (injR_nonint 3.0%R n).
      * eapply fir_cons_nonint.
        { intro n. exact (injR_nonint 1.5%R n). }
        { constructor. }
Qed.