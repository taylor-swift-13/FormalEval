Here is the full content of the Coq output file with the corrected definitions and the new test case proof.

```coq
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.

Definition int := Z.

Inductive Any : Type :=
| AnyInt (i : int)
| AnyReal (r : R)
| AnyStr (s : string).

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt i => i = n
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
    [AnyInt 1%Z; AnyInt 2%Z; AnyInt 4%Z; AnyStr "four"%string; AnyReal 5.5%R; AnyInt 6%Z; AnyStr "33"%string; AnyStr "seven"%string; AnyStr "8"%string] 
    [1%Z; 2%Z; 4%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z).
  - simpl. reflexivity.
  - apply fir_cons_int with (n := 2%Z).
    + simpl. reflexivity.
    + apply fir_cons_int with (n := 4%Z).
      * simpl. reflexivity.
      * apply fir_cons_nonint.
        -- intros n H. simpl in H. contradiction.
        -- apply fir_cons_nonint.
           ++ intros n H. simpl in H. contradiction.
           ++ apply fir_cons_int with (n := 6%Z).
              ** simpl. reflexivity.
              ** apply fir_cons_nonint.
                 --- intros n H. simpl in H. contradiction.
                 --- apply fir_cons_nonint.
                     +++ intros n H. simpl in H. contradiction.
                     +++ apply fir_cons_nonint.
                         *** intros n H. simpl in H. contradiction.
                         *** apply fir_nil.
Qed.