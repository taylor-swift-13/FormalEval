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

Parameter v1 vlist1 v2 vstr3 vreal56 vempty1 vset vtrue1 vtrue2 vlist2 vempty2 vtrue3 : Any.

Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v2 : IsInt v2 2%Z.

Axiom NonInt_vlist1 : forall n, ~ IsInt vlist1 n.
Axiom NonInt_vstr3 : forall n, ~ IsInt vstr3 n.
Axiom NonInt_vreal56 : forall n, ~ IsInt vreal56 n.
Axiom NonInt_vempty1 : forall n, ~ IsInt vempty1 n.
Axiom NonInt_vset : forall n, ~ IsInt vset n.
Axiom NonInt_vtrue1 : forall n, ~ IsInt vtrue1 n.
Axiom NonInt_vtrue2 : forall n, ~ IsInt vtrue2 n.
Axiom NonInt_vlist2 : forall n, ~ IsInt vlist2 n.
Axiom NonInt_vempty2 : forall n, ~ IsInt vempty2 n.
Axiom NonInt_vtrue3 : forall n, ~ IsInt vtrue3 n.

Example test_case_new:
  filter_integers_spec
    [v1; vlist1; v2; vstr3; vreal56; vempty1; vset; vtrue1; vtrue2; vlist2; vempty2; vtrue3]
    [1%Z; 2%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1 |].
  eapply fir_cons_nonint; [apply NonInt_vlist1 |].
  eapply fir_cons_int; [apply IsInt_v2 |].
  eapply fir_cons_nonint; [apply NonInt_vstr3 |].
  eapply fir_cons_nonint; [apply NonInt_vreal56 |].
  eapply fir_cons_nonint; [apply NonInt_vempty1 |].
  eapply fir_cons_nonint; [apply NonInt_vset |].
  eapply fir_cons_nonint; [apply NonInt_vtrue1 |].
  eapply fir_cons_nonint; [apply NonInt_vtrue2 |].
  eapply fir_cons_nonint; [apply NonInt_vlist2 |].
  eapply fir_cons_nonint; [apply NonInt_vempty2 |].
  eapply fir_cons_nonint; [apply NonInt_vtrue3 |].
  constructor.
Qed.