one sig FSM {
  start: set State,
  stop: set State
}

sig State {
  transition: set State
}

// Part (a)
fact OneStartAndStop {
  // FSM only has one start state.
  all start1, start2 : FSM.start | start1 = start2

  // FSM only has one stop state.
  all stop1, stop2 : FSM.stop | stop1 = stop2

  // DO YOU WANT TO ENFORCE THAT THERE IS ALWAYS A STOP STATE?
  some FSM.stop
  // Note: It's fine if the student does not state "one FSM.start" because it is implied.
}

// Part (b)
fact ValidStartAndStop {
  // A state cannot be both a start state and a stop state.
  FSM.start !in FSM.stop

  // No transition ends at the start state.
  // Fix: replace "s.transition !in FSM.start" with "FSM.start !in s.transition".
  all s: State | s.transition !in FSM.start

  // MV: If no transition then stop state
  // Fix: replace "=>" with "<=>".
  all s: State | s.transition = none => s in FSM.stop
}

// Part (c)
fact Reachability {
  // All states are reachable from the start state.
  State = FSM.start.*transition

  // The stop state is reachable from any state.
  all s: State | FSM.stop in s.*transition
}

run {} for 5

val test3 {
some disj FSM0: FSM {some disj State0, State1: State {
FSM = FSM0
start = FSM0->State1
stop = FSM0->State0
State = State0 + State1
transition = State1->State0
}}
}
@Test test3: run test3 for 3 expect 1

val test7 {
some disj FSM0: FSM {some disj State0, State1, State2: State {
FSM = FSM0
start = FSM0->State1 + FSM0->State2
stop = FSM0->State0
State = State0 + State1 + State2
transition = State1->State0 + State2->State0
}}
}
@Test test7: run test7 for 3 expect 0

val test4 {
some disj FSM0: FSM {some disj State0, State1, State2: State {
FSM = FSM0
start = FSM0->State1
stop = FSM0->State0
State = State0 + State1 + State2
transition = State1->State2 + State2->State0 + State2->State2
}}
}
@Test test4: run test4 for 3 expect 1

val test5 {
some disj FSM0: FSM {some disj State0, State1: State {
FSM = FSM0
start = FSM0->State0
stop = FSM0->State1
State = State0 + State1
transition = State0->State1
}}
}
@Test test5: run test5 for 3 expect 1

val test12 {
some disj FSM0: FSM {some disj State0, State1: State {
FSM = FSM0
start = FSM0->State1
stop = FSM0->State0
State = State0 + State1
transition = State0->State0 + State1->State0
}}
}
@Test test12: run test12 for 3 expect 0

val test11 {
some disj FSM0: FSM {some disj State0, State1: State {
FSM = FSM0
start = FSM0->State1
stop = FSM0->State0
State = State0 + State1
transition = State1->State0 + State1->State1
}}
}
@Test test11: run test11 for 3 expect 0

val test1 {
some disj FSM0, FSM1: FSM {some disj State0, State1, State2: State {
FSM = FSM0 + FSM1
start = FSM0->State2 + FSM1->State2
stop = FSM1->State1
State = State0 + State1 + State2
transition = State0->State1 + State2->State0 + State2->State1
}}
}
@Test test1: run test1 for 3 expect 0

val test6 {
some disj FSM0: FSM {some disj State0, State1: State {
FSM = FSM0
start = FSM0->State1
no stop
State = State0 + State1
transition = State0->State0 + State1->State0
}}
}
@Test test6: run test6 for 3 expect 0

val test2 {
some disj FSM0, FSM1: FSM {some disj State0, State1: State {
FSM = FSM0 + FSM1
start = FSM1->State1
stop = FSM1->State0
State = State0 + State1
transition = State1->State0
}}
}
@Test test2: run test2 for 3 expect 0

val test9 {
some disj FSM0: FSM {some disj State0, State1: State {
FSM = FSM0
start = FSM0->State1
stop = FSM0->State0
State = State0 + State1
transition = State0->State0 + State1->State0 + State1->State1
}}
}
@Test test9: run test9 for 3 expect 0

val test15 {
some disj FSM0: FSM {some disj State0, State1, State2: State {
FSM = FSM0
start = FSM0->State2
stop = FSM0->State1
State = State0 + State1 + State2
transition = State0->State0 + State2->State0 + State2->State1
}}
}
@Test test15: run test15 for 3 expect 0

val test10 {
some disj FSM0: FSM {some disj State0: State {
FSM = FSM0
start = FSM0->State0
stop = FSM0->State0
State = State0
no transition
}}
}
@Test test10: run test10 for 3 expect 0

val test14 {
some disj FSM0: FSM {some disj State0, State1, State2: State {
FSM = FSM0
start = FSM0->State2
stop = FSM0->State1
State = State0 + State1 + State2
transition = State0->State1 + State2->State1
}}
}
@Test test14: run test14 for 3 expect 0

val test8 {
some disj FSM0: FSM {some disj State0, State1, State2: State {
FSM = FSM0
start = FSM0->State2
no stop
State = State0 + State1 + State2
transition = State1->State1 + State2->State0 + State2->State1
}}
}
@Test test8: run test8 for 3 expect 0

val test13 {
some disj FSM0: FSM {some disj State0, State1: State {
FSM = FSM0
start = FSM0->State1
stop = FSM0->State0
State = State0 + State1
no transition
}}
}
@Test test13: run test13 for 3 expect 0