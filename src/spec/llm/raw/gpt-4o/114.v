
Require Import List.
Require Import ZArith.

Open Scope Z_scope.

Definition minSubArraySum_spec (nums : list Z) (min_sum : Z) : Prop :=
  (forall x, In x nums -> x >= 0) -> min_sum = fold_right Z.min 0 nums /\
  (exists subarray, subarray <> nil /\ subarray = filter (fun x => x < 0) nums /\ min_sum = fold_right Z.add 0 subarray) \/
  (forall subarray, subarray <> nil -> subarray = filter (fun x => x < 0) nums -> min_sum <= fold_right Z.add 0 subarray).
