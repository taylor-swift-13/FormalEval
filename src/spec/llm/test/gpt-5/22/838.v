Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter v2 : Any.
Parameter v_eighEWGKODIt : Any.
Parameter v3 : Any.
Parameter v_four1 : Any.
Parameter v_5_5R : Any.
Parameter v5a : Any.
Parameter v_35_50077440707028R : Any.
Parameter v_seven : Any.
Parameter v_8_str : Any.
Parameter v_9_0R1 : Any.
Parameter v_9_0R2 : Any.
Parameter v_four2 : Any.
Parameter v5b : Any.

Axiom IsInt_v2 : IsInt v2 2%Z.
Axiom IsInt_v3 : IsInt v3 3%Z.
Axiom IsInt_v5a : IsInt v5a 5%Z.
Axiom IsInt_v5b : IsInt v5b 5%Z.

Axiom NonInt_v_eighEWGKODIt : forall n, ~ IsInt v_eighEWGKODIt n.
Axiom NonInt_v_four1 : forall n, ~ IsInt v_four1 n.
Axiom NonInt_v_5_5R : forall n, ~ IsInt v_5_5R n.
Axiom NonInt_v_35_50077440707028R : forall n, ~ IsInt v_35_50077440707028R n.
Axiom NonInt_v_seven : forall n, ~ IsInt v_seven n.
Axiom NonInt_v_8_str : forall n, ~ IsInt v_8_str n.
Axiom NonInt_v_9_0R1 : forall n, ~ IsInt v_9_0R1 n.
Axiom NonInt_v_9_0R2 : forall n, ~ IsInt v_9_0R2 n.
Axiom NonInt_v_four2 : forall n, ~ IsInt v_four2 n.

Example test_case_new:
  filter_integers_spec
    [v2; v_eighEWGKODIt; v3; v_four1; v_5_5R; v5a; v_35_50077440707028R; v_seven; v_8_str; v_9_0R1; v_9_0R2; v_four2; v5b]
    [2%Z; 3%Z; 5%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v2|].
  eapply fir_cons_nonint; [apply NonInt_v_eighEWGKODIt|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_nonint; [apply NonInt_v_four1|].
  eapply fir_cons_nonint; [apply NonInt_v_5_5R|].
  eapply fir_cons_int; [apply IsInt_v5a|].
  eapply fir_cons_nonint; [apply NonInt_v_35_50077440707028R|].
  eapply fir_cons_nonint; [apply NonInt_v_seven|].
  eapply fir_cons_nonint; [apply NonInt_v_8_str|].
  eapply fir_cons_nonint; [apply NonInt_v_9_0R1|].
  eapply fir_cons_nonint; [apply NonInt_v_9_0R2|].
  eapply fir_cons_nonint; [apply NonInt_v_four2|].
  eapply fir_cons_int; [apply IsInt_v5b|].
  constructor.
Qed.