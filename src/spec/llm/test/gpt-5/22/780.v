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

Parameters v0 v_s2 v_s22 v_obj v_list123 v_list4m77m77 v_list4m77m77_2 : Any.
Axiom v0_is_int : IsInt v0 0%Z.
Axiom v_s2_nonint : forall n, ~ IsInt v_s2 n.
Axiom v_s22_nonint : forall n, ~ IsInt v_s22 n.
Axiom v_obj_nonint : forall n, ~ IsInt v_obj n.
Axiom v_list123_nonint : forall n, ~ IsInt v_list123 n.
Axiom v_list4m77m77_nonint : forall n, ~ IsInt v_list4m77m77 n.
Axiom v_list4m77m77_2_nonint : forall n, ~ IsInt v_list4m77m77_2 n.

Example test_case_mixed: filter_integers_spec [v0; v_s2; v_s22; v_obj; v_list123; v_list4m77m77; v_list4m77m77_2] [0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v0_is_int|].
  eapply fir_cons_nonint; [apply v_s2_nonint|].
  eapply fir_cons_nonint; [apply v_s22_nonint|].
  eapply fir_cons_nonint; [apply v_obj_nonint|].
  eapply fir_cons_nonint; [apply v_list123_nonint|].
  eapply fir_cons_nonint; [apply v_list4m77m77_nonint|].
  eapply fir_cons_nonint; [apply v_list4m77m77_2_nonint|].
  constructor.
Qed.