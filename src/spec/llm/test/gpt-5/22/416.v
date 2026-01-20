Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter val_int : Z -> Any.
Parameter val_list : list Any -> Any.
Parameter val_string : string -> Any.

Axiom IsInt_val_int : forall z, IsInt (val_int z) z.
Axiom NonInt_val_list : forall l n, ~ IsInt (val_list l) n.
Axiom NonInt_val_string : forall s n, ~ IsInt (val_string s) n.

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

Example test_case_mixed:
  filter_integers_spec
    [
      val_int 1%Z;
      val_list [val_int 2%Z; val_string "3"];
      val_list [val_int 4%Z; val_int 4%Z];
      val_list [val_int 5%Z; val_int 6%Z; val_int 6%Z];
      val_list [val_int 7%Z; val_int 8%Z];
      val_int 9%Z;
      val_int (-6)%Z;
      val_int 1%Z;
      val_int 1%Z;
      val_int 9%Z
    ]
    [
      1%Z;
      9%Z;
      (-6)%Z;
      1%Z;
      1%Z;
      9%Z
    ].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_val_int |].
  eapply fir_cons_nonint; [intros n; apply (NonInt_val_list [val_int 2%Z; val_string "3"]) |].
  eapply fir_cons_nonint; [intros n; apply (NonInt_val_list [val_int 4%Z; val_int 4%Z]) |].
  eapply fir_cons_nonint; [intros n; apply (NonInt_val_list [val_int 5%Z; val_int 6%Z; val_int 6%Z]) |].
  eapply fir_cons_nonint; [intros n; apply (NonInt_val_list [val_int 7%Z; val_int 8%Z]) |].
  eapply fir_cons_int; [apply IsInt_val_int |].
  eapply fir_cons_int; [apply IsInt_val_int |].
  eapply fir_cons_int; [apply IsInt_val_int |].
  eapply fir_cons_int; [apply IsInt_val_int |].
  eapply fir_cons_int; [apply IsInt_val_int |].
  constructor.
Qed.