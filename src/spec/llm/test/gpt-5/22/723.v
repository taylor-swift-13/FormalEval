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

Parameters v20 v1 v9a v9b w1 w2 w3 w4 w5 w6 w7 : Any.
Axiom IsInt_v20 : IsInt v20 20%Z.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v9a : IsInt v9a 9%Z.
Axiom IsInt_v9b : IsInt v9b 9%Z.
Axiom NotInt_w1 : forall n, ~ IsInt w1 n.
Axiom NotInt_w2 : forall n, ~ IsInt w2 n.
Axiom NotInt_w3 : forall n, ~ IsInt w3 n.
Axiom NotInt_w4 : forall n, ~ IsInt w4 n.
Axiom NotInt_w5 : forall n, ~ IsInt w5 n.
Axiom NotInt_w6 : forall n, ~ IsInt w6 n.
Axiom NotInt_w7 : forall n, ~ IsInt w7 n.

Example test_case_nested: filter_integers_spec [v20; v1; w1; w2; w3; w4; w5; w6; v9a; v9b; w7] [20%Z; 1%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_v20|].
  eapply fir_cons_int; [exact IsInt_v1|].
  eapply fir_cons_nonint; [exact NotInt_w1|].
  eapply fir_cons_nonint; [exact NotInt_w2|].
  eapply fir_cons_nonint; [exact NotInt_w3|].
  eapply fir_cons_nonint; [exact NotInt_w4|].
  eapply fir_cons_nonint; [exact NotInt_w5|].
  eapply fir_cons_nonint; [exact NotInt_w6|].
  eapply fir_cons_int; [exact IsInt_v9a|].
  eapply fir_cons_int; [exact IsInt_v9b|].
  eapply fir_cons_nonint; [exact NotInt_w7|].
  constructor.
Qed.