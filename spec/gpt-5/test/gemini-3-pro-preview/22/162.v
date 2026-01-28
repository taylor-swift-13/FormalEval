Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition int := Z.

Inductive Any : Type :=
| AnyInt (z : Z)
| AnyString (s : string)
| AnyFloat (r : R).

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt z => z = n
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm.
  destruct v; simpl in *; try contradiction.
  subst. reflexivity.
Qed.

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

Example test_filter_integers : 
  filter_integers_spec 
    [AnyInt 0%Z; AnyInt 2%Z; AnyInt 3%Z; AnyString "four"; AnyFloat 5.5%R; AnyInt 6%Z; AnyString "seven"; AnyString "8"; AnyFloat 9.0%R] 
    [0%Z; 2%Z; 3%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 0%Z). simpl. reflexivity.
  apply fir_cons_int with (n := 2%Z). simpl. reflexivity.
  apply fir_cons_int with (n := 3%Z). simpl. reflexivity.
  apply fir_cons_nonint. intros n H. simpl in H. contradiction.
  apply fir_cons_nonint. intros n H. simpl in H. contradiction.
  apply fir_cons_int with (n := 6%Z). simpl. reflexivity.
  apply fir_cons_nonint. intros n H. simpl in H. contradiction.
  apply fir_cons_nonint. intros n H. simpl in H. contradiction.
  apply fir_cons_nonint. intros n H. simpl in H. contradiction.
  apply fir_nil.
Qed.