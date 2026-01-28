Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.

Open Scope Z_scope.
Open Scope string_scope.

Definition fruit_distribution_spec (s : string) (n : Z) (mangoes : Z) : Prop :=
  let words := True in
  (* Parsing the number of apples and oranges from s as c1 and c2 *)
  (* For specification purposes, we express their existence and values abstractly *)
  exists c1 c2 : Z,
    (* c1 and c2 correspond to the first and fourth tokens parsed as integers *)
    (* The string s is of the form "<c1> apples and <c2> oranges" *)
    (* So c1 and c2 are nonnegative integers *)
    0 <= c1 /\ 0 <= c2 /\
    (* The total fruit count minus apples and oranges must be nonnegative *)
    n - c1 - c2 >= 0 /\
    (* mangoes is the difference *)
    mangoes = n - c1 - c2.

Example test_fruit_distribution : 
  fruit_distribution_spec "10 apples and 5 oranges" 31 16.
Proof.
  unfold fruit_distribution_spec.
  (* Instantiate c1 and c2 with the parsed values 10 and 5 *)
  exists 10, 5.
  (* Prove the arithmetic properties *)
  repeat split; try lia.
Qed.