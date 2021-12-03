From iris.heap_lang.lib Require Export array.
From reloc Require Export reloc.
From reloc.examples.folly_queue Require Export singleElementQueue.

Definition enqueue : val := λ: "slots" "cap" "ticket_" "v",
  let: "ticket" := FAA "ticket_" #1 in
  let: "turn" := "ticket" `quot` "cap" in
  let: "idx" := "ticket" `rem` "cap" in
  enqueueWithTicket (!("slots" +ₗ "idx")) "turn" "v".

Definition dequeue : val := λ: "slots" "cap" "ticket_",
  let: "ticket" := FAA "ticket_" #1 in
  let: "turn" := "ticket" `quot` "cap" in
  let: "idx" := "ticket" `rem` "cap" in
  dequeueWithTicket (!("slots" +ₗ "idx")) "turn".

Definition newSQueue : val := λ: <>,
  let: "r" := ref NONE in
  let: "t" := newTS #() in
  ("t", "r").

Definition newQueue : val := λ: "q", Λ:
  let: "slots" := array_init "q" newSQueue in
  let: "pushTicket" := ref #0 in
  let: "popTicket"  := ref #0 in
  (λ: "v", enqueue "slots" "q" "pushTicket" "v",
   λ: <>, dequeue "slots" "q" "popTicket").
