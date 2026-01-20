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

Parameter one : Any.
Axiom one_is_int : IsInt one 1%Z.

Parameter str2 : Any.
Axiom str2_nonint : forall n, ~ IsInt str2 n.

Parameter empty_obj : Any.
Axiom empty_obj_nonint : forall n, ~ IsInt empty_obj n.

Parameter list123 : Any.
Axiom list123_nonint : forall n, ~ IsInt list123 n.

Parameter list45 : Any.
Axiom list45_nonint : forall n, ~ IsInt list45 n.

Parameter dict_six_6 : Any.
Axiom dict_six_6_nonint : forall n, ~ IsInt dict_six_6 n.

Parameter list123_2 : Any.
Axiom list123_2_nonint : forall n, ~ IsInt list123_2 n.

Example test_case_mixed: filter_integers_spec [one; str2; empty_obj; list123; list45; dict_six_6; list123_2] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply one_is_int |].
  eapply fir_cons_nonint; [apply str2_nonint |].
  eapply fir_cons_nonint; [apply empty_obj_nonint |].
  eapply fir_cons_nonint; [apply list123_nonint |].
  eapply fir_cons_nonint; [apply list45_nonint |].
  eapply fir_cons_nonint; [apply dict_six_6_nonint |].
  eapply fir_cons_nonint; [apply list123_2_nonint |].
  constructor.
Qed.