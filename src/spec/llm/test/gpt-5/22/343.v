Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Any.
Parameter Hnon1 : forall n, ~ IsInt a1 n.
Parameter Hint2 : IsInt a2 2%Z.
Parameter Hnon3 : forall n, ~ IsInt a3 n.
Parameter Hnon4 : forall n, ~ IsInt a4 n.
Parameter Hnon5 : forall n, ~ IsInt a5 n.
Parameter Hnon6 : forall n, ~ IsInt a6 n.
Parameter Hint7 : IsInt a7 1%Z.
Parameter Hnon8 : forall n, ~ IsInt a8 n.
Parameter Hnon9 : forall n, ~ IsInt a9 n.
Parameter Hnon10 : forall n, ~ IsInt a10 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] [2%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply Hnon1 |].
  eapply fir_cons_int; [apply Hint2 |].
  eapply fir_cons_nonint; [apply Hnon3 |].
  eapply fir_cons_nonint; [apply Hnon4 |].
  eapply fir_cons_nonint; [apply Hnon5 |].
  eapply fir_cons_nonint; [apply Hnon6 |].
  eapply fir_cons_int; [apply Hint7 |].
  eapply fir_cons_nonint; [apply Hnon8 |].
  eapply fir_cons_nonint; [apply Hnon9 |].
  eapply fir_cons_nonint; [apply Hnon10 |].
  apply fir_nil.
Qed.