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

Parameter a_8seven : Any.
Parameter a_2a : Any.
Parameter a_false : Any.
Parameter a_2b : Any.
Parameter a_3a : Any.
Parameter a_four : Any.
Parameter a_3b : Any.
Parameter a_5p5 : Any.
Parameter a_6 : Any.
Parameter a_seven : Any.
Parameter a_8str1 : Any.
Parameter a_9p0 : Any.
Parameter a_8str2 : Any.

Axiom nonint_8seven : forall n, ~ IsInt a_8seven n.
Axiom isint_2a : IsInt a_2a 2%Z.
Axiom nonint_false : forall n, ~ IsInt a_false n.
Axiom isint_2b : IsInt a_2b 2%Z.
Axiom isint_3a : IsInt a_3a 3%Z.
Axiom nonint_four : forall n, ~ IsInt a_four n.
Axiom isint_3b : IsInt a_3b 3%Z.
Axiom nonint_5p5 : forall n, ~ IsInt a_5p5 n.
Axiom isint_6 : IsInt a_6 6%Z.
Axiom nonint_seven : forall n, ~ IsInt a_seven n.
Axiom nonint_8str1 : forall n, ~ IsInt a_8str1 n.
Axiom nonint_9p0 : forall n, ~ IsInt a_9p0 n.
Axiom nonint_8str2 : forall n, ~ IsInt a_8str2 n.

Example test_case_filter:
  filter_integers_spec
    [a_8seven; a_2a; a_false; a_2b; a_3a; a_four; a_3b; a_5p5; a_6; a_seven; a_8str1; a_9p0; a_8str2]
    [2%Z; 2%Z; 3%Z; 3%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_8seven |].
  eapply fir_cons_int; [apply isint_2a |].
  eapply fir_cons_nonint; [apply nonint_false |].
  eapply fir_cons_int; [apply isint_2b |].
  eapply fir_cons_int; [apply isint_3a |].
  eapply fir_cons_nonint; [apply nonint_four |].
  eapply fir_cons_int; [apply isint_3b |].
  eapply fir_cons_nonint; [apply nonint_5p5 |].
  eapply fir_cons_int; [apply isint_6 |].
  eapply fir_cons_nonint; [apply nonint_seven |].
  eapply fir_cons_nonint; [apply nonint_8str1 |].
  eapply fir_cons_nonint; [apply nonint_9p0 |].
  eapply fir_cons_nonint; [apply nonint_8str2 |].
  constructor.
Qed.