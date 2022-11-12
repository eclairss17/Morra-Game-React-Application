'reach 0.1';

const[gameOutcome, Player1_WINS, DRAW, Player2_WINS] = makeEnum(3);

const winner = function(player1Hand, player2Hand, predict1, predict2)
{
    
    const totalHands = player1Hand + player2Hand;

    const player1Correct = (predict1 == totalHands ? true : false);
    const player2Correct = (predict2 == totalHands ? true : false);

    if (player1Correct && !player2Correct)
    {
        return Player1_WINS;
    }
    else if (!player1Correct && player2Correct)
    {
        return Player2_WINS;
    }
    else 
    {
        return DRAW;
    }

}

assert(winner(0, 4, 0, 4) == Player2_WINS);
assert(winner(4, 0, 4, 0) == Player1_WINS);
assert(winner(0, 5, 0, 4) == DRAW);
assert(winner(1,2,1,2) == DRAW);

forall(UInt, playsHandA =>
    forall(UInt, playsHandB =>
      forall(UInt, gHandA =>
        forall(UInt, gHandB =>
          assert(gameOutcome(winner(playsHandA, playsHandB, gHandA, gHandB)))))));
  
  forall(UInt, playsHandA =>
    forall(UInt, playsHandB =>
      forall(UInt, sameGuess =>
        assert(winner(playsHandA, playsHandB, sameGuess, sameGuess) == DRAW))));
  

const Player = {
    ...hasRandom,
    getHand: Fun([], UInt),
    getPrediction: Fun([], UInt),
    seeGameOutcome: Fun([UInt], Null),
    informTimeout: Fun([], Null),
    
};

export const main = Reach.App(() => {
    const Deployer = Participant('p1', {
        ...Player,
        wager:UInt,
        deadline: UInt,
        //getContinue: Fun([], Bool),

    });

    const Attacher = Participant('p2', {
        ...Player,
        acceptWager: Fun([UInt], Null),
        //acceptContinue: Fun([], Bool),
    });
    init();

    const informTimeout = () => {
        each([Deployer, Attacher], () => {
            interact.informTimeout();
        });
    }

    Deployer.only(() => {
        const wager = declassify(interact.wager);
        const deadline = declassify(interact.deadline);
    })

    Deployer.publish(wager, deadline)
        .pay(wager);
    commit();

    Attacher.only(() => {

        interact.acceptWager(wager);
    });

    Attacher.pay(wager)
        .timeout(relativeTime(deadline), () => closeTo(Deployer, informTimeout));

    var ifOutcome = DRAW;

    invariant(balance() == 2 * wager && (ifOutcome == DRAW || ifOutcome == Player1_WINS || ifOutcome == Player2_WINS));

    while ( ifOutcome == DRAW )
    {
        commit();

        Deployer.only(() =>{
            const _handD = interact.getHand();
            const _predictionD = interact.getPrediction();
            const [_commitHandD, _saltHandD] = makeCommitment(interact, _handD);
            const [_commitPredictionD, _saltPredictionD] = makeCommitment(interact, _predictionD);

            const commitHandD = declassify(_commitHandD);
            const commitPredictionD = declassify(_commitPredictionD);
        });

        Deployer.publish(commitHandD, commitPredictionD)
            .timeout(relativeTime(deadline), () => closeTo(Attacher, informTimeout));

        commit();

        unknowable(Attacher, Deployer(_handD, _saltHandD));

        Attacher.only(()=> {
            const handA = declassify(interact.getHand());
            const predictionA = declassify(interact.getPrediction());
        });

        Attacher.publish(handA, predictionA)
            .timeout(relativeTime(deadline), () => closeTo(Deployer, informTimeout));
        commit();


        Deployer.only(() => {
            const [saltHandD, handD] = declassify([_saltHandD, _handD]);
            
            const [saltPredictionD, predictionD ] = declassify([_saltPredictionD, _predictionD ]);
            
        });

        Deployer.publish(saltHandD, handD, saltPredictionD, predictionD)
            .timeout(relativeTime(deadline), () => closeTo(Attacher, informTimeout));
        
        
        checkCommitment(commitHandD, saltHandD, handD);
        checkCommitment(commitPredictionD, saltPredictionD, predictionD)

        ifOutcome = winner(handD, handA, predictionD, predictionA);
        continue;
    }

    assert(ifOutcome == Player1_WINS || ifOutcome == Player2_WINS);
    
    transfer(2*wager).to(ifOutcome==Player1_WINS ? Deployer : Attacher);
    
    commit();

    each([Attacher, Deployer], () => 
    {
        interact.seeGameOutcome(ifOutcome);
    });

    exit();
});