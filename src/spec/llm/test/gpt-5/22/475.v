Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter IntAny : int -> Any.
Parameter ListAny : list Any -> Any.
Parameter StringAny : string -> Any.
Parameter ObjectAny : Any.

Axiom IsInt_IntAny : forall z, IsInt (IntAny z) z.
Axiom IsInt_ListAny_false : forall l n, ~ IsInt (ListAny l) n.
Axiom IsInt_StringAny_false : forall s n, ~ IsInt (StringAny s) n.
Axiom IsInt_ObjectAny_false : forall n, ~ IsInt ObjectAny n.

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

Example test_case_new:
  filter_integers_spec
    [ IntAny 1%Z;
      ListAny [IntAny 2%Z; IntAny 3%Z];
      IntAny 4%Z;
      ListAny [IntAny 5%Z];
      IntAny 1%Z;
      ListAny [IntAny 7%Z; StringAny "8"%string];
      ObjectAny;
      StringAny "9rHiG"%string;
      StringAny "9"%string;
      ListAny [IntAny 5%Z]
    ]
    [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int with (n := 1%Z).
  - apply IsInt_IntAny.
  - eapply fir_cons_nonint.
    + intros n H. exact (IsInt_ListAny_false [IntAny 2%Z; IntAny 3%Z] n H).
    + eapply fir_cons_int with (n := 4%Z).
      * apply IsInt_IntAny.
      * eapply fir_cons_nonint.
        { intros n H. exact (IsInt_ListAny_false [IntAny 5%Z] n H). }
        eapply fir_cons_int with (n := 1%Z).
        { apply IsInt_IntAny. }
        eapply fir_cons_nonint.
        { intros n H. exact (IsInt_ListAny_false [IntAny 7%Z; StringAny "8"%string] n H). }
        eapply fir_cons_nonint.
        { intros n H. exact (IsInt_ObjectAny_false n H). }
        eapply fir_cons_nonint.
        { intros n H. exact (IsInt_StringAny_false "9rHiG"%string n H). }
        eapply fir_cons_nonint.
        { intros n H. exact (IsInt_StringAny_false "9"%string n H). }
        eapply fir_cons_nonint.
        { intros n H. exact (IsInt_ListAny_false [IntAny 5%Z] n H). }
        constructor.
Qed.