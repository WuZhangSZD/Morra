'reach 0.1';

const [ isFinger, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);
const [isGuess, GUESS0, GUESS1, GUESS2, GUESS3, GUESS4, GUESS5, GUESS6, GUESS7, GUESS8, GUESS9, GUESS10]=makeEnum(11);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

const winner = (fingerAlice,fingerBob,guessAlice,guessBob) => {
  const total=fingerAlice+fingerBob;
  if(guessAlice==guessBob)
  {
    const outcome=DRAW;
    return outcome;
  }
  else
  {
    if(total==guessAlice)
    {
      const outcome=A_WINS;
      return outcome;
    }else{
      if(total==guessBob)
      {
        const outcome=B_WINS;
        return outcome;
      }
      else
      {
        const outcome=DRAW;
        return outcome;
      }
    }
  }
  
}

assert(winner(ONE,ONE, GUESS2,GUESS0) == A_WINS);
assert(winner(ONE,ONE, GUESS0,GUESS2) == B_WINS);
assert(winner(ONE,ONE, GUESS0,GUESS0) == DRAW);
assert(winner(ONE,ONE, GUESS1,GUESS0) == DRAW);


forall(UInt, fingerAlice =>
  forall(UInt, fingerBob =>
    forall(UInt, guessAlice=>
      forall(UInt, guessBob=>
        assert(isOutcome(winner(fingerAlice, fingerBob,guessAlice,guessBob)))))));

forall(UInt, (fingerAlice)=>
  forall(UInt,(fingerBob)=>
    forall(UInt,(guess) =>
      assert(winner(fingerAlice, fingerBob,guess,guess) == DRAW))));

const Player = {
  ...hasRandom,
  getFinger: Fun([], UInt),
  getGuess: Fun([], UInt),
  seeOutcome: Fun([UInt], Null),
  informTimeout: Fun([], Null),
};

export const main = Reach.App(() => {
  const Alice = Participant('Alice', {
    ...Player,
    wager: UInt, // atomic units of currency
    deadline: UInt, // time delta (blocks/rounds)
  });
  const Bob   = Participant('Bob', {
    ...Player,
    acceptWager: Fun([UInt], Null),
  });
  init();

  const informTimeout = () => {
    each([Alice, Bob], () => {
      interact.informTimeout();
    });
  };

  Alice.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });
  Alice.publish(wager, deadline)
    .pay(wager);
  commit();

  Bob.only(() => {
    interact.acceptWager(wager);
  });
  Bob.pay(wager)
    .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));

  var outcome = DRAW;
  invariant( balance() == 2 * wager && isOutcome(outcome) );
  while ( outcome == DRAW ) {
    commit();

    Alice.only(() => {
      const _fingerAlice = interact.getFinger();
      const _guessAlice = interact.getGuess();
      const [_commitAlice, _saltAlice] = makeCommitment(interact, _fingerAlice);
      const [_commitAlice2,_saltAlice2] = makeCommitment (interact, _guessAlice);
      const commitAlice = declassify(_commitAlice);
      const commitAlice2=declassify(_commitAlice2);
    });
    Alice.publish(commitAlice,commitAlice2)
      .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
    commit();

    unknowable(Bob, Alice(_fingerAlice,_guessAlice, _saltAlice,_saltAlice2));
    Bob.only(() => {
      const fingerBob = declassify(interact.getFinger());
      const guessBob = declassify(interact.getGuess());
    });
    Bob.publish(fingerBob,guessBob)
      .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));
    commit();

    Alice.only(() => {
      const saltAlice = declassify(_saltAlice);
      const saltAlice2 = declassify(_saltAlice2);
      const fingerAlice = declassify(_fingerAlice);
      const guessAlice = declassify(_guessAlice);
    });
    Alice.publish(saltAlice,saltAlice2, fingerAlice, guessAlice)
      .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
    checkCommitment(commitAlice, saltAlice, fingerAlice);
    checkCommitment(commitAlice2, saltAlice2, guessAlice);

    outcome = winner(fingerAlice, fingerBob,guessAlice,guessBob);
    continue;
  }

  assert(outcome == A_WINS || outcome == B_WINS);
  transfer(2 * wager).to(outcome == A_WINS ? Alice : Bob);
  commit();

  each([Alice, Bob], () => {
    interact.seeOutcome(outcome);
  });
});