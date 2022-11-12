// Automatically generated with Reach 0.1.12 (0b231964)
/* eslint-disable */
export const _version = '0.1.12';
export const _versionHash = '0.1.12 (0b231964)';
export const _backendVersion = 25;

export function getExports(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getEvents(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getViews(s, viewlib) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Address;
  const ctc1 = stdlib.T_UInt;
  const ctc2 = stdlib.T_Digest;
  
  return {
    infos: {
      },
    views: {
      1: [ctc0, ctc1, ctc1, ctc1],
      5: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc1],
      7: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc2, ctc2, ctc1],
      9: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc2, ctc2, ctc1, ctc1, ctc1]
      }
    };
  
  };
export function _getMaps(s) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Tuple([]);
  return {
    mapDataTy: ctc0
    };
  };
export async function p1(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for p1 expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for p1 expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Digest;
  const ctc2 = stdlib.T_Null;
  const ctc3 = stdlib.T_Address;
  
  
  const v373 = stdlib.protect(ctc0, interact.deadline, 'for p1\'s interact field deadline');
  const v374 = stdlib.protect(ctc0, interact.wager, 'for p1\'s interact field wager');
  
  const txn1 = await (ctc.sendrecv({
    args: [v374, v373],
    evt_cnt: 2,
    funcNum: 0,
    lct: stdlib.checkedBigNumberify('./index.rsh:81:14:dot', stdlib.UInt_max, '0'),
    onlyIf: true,
    out_tys: [ctc0, ctc0],
    pay: [v374, []],
    sim_p: (async (txn1) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v378, v379], secs: v381, time: v380, didSend: v89, from: v377 } = txn1;
      
      sim_r.txns.push({
        amt: v378,
        kind: 'to',
        tok: undefined /* Nothing */
        });
      const v390 = stdlib.safeAdd(v380, v379);
      sim_r.isHalt = false;
      
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: undefined /* mto */,
    tys: [ctc0, ctc0],
    waitIfNotPresent: false
    }));
  const {data: [v378, v379], secs: v381, time: v380, didSend: v89, from: v377 } = txn1;
  ;
  const v390 = stdlib.safeAdd(v380, v379);
  const txn2 = await (ctc.recv({
    didSend: false,
    evt_cnt: 0,
    funcNum: 1,
    out_tys: [],
    timeoutAt: ['time', v390],
    waitIfNotPresent: false
    }));
  if (txn2.didTimeout) {
    const txn3 = await (ctc.sendrecv({
      args: [v377, v378, v379, v390],
      evt_cnt: 0,
      funcNum: 2,
      lct: v380,
      onlyIf: true,
      out_tys: [],
      pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
      sim_p: (async (txn3) => {
        const sim_r = { txns: [], mapRefs: [], maps: [] };
        let sim_txn_ctr = stdlib.UInt_max;
        const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
        
        
        const {data: [], secs: v564, time: v563, didSend: v310, from: v562 } = txn3;
        
        ;
        sim_r.txns.push({
          kind: 'from',
          to: v377,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        
        return sim_r;
        }),
      soloSend: false,
      timeoutAt: undefined /* mto */,
      tys: [ctc3, ctc0, ctc0, ctc0],
      waitIfNotPresent: false
      }));
    const {data: [], secs: v564, time: v563, didSend: v310, from: v562 } = txn3;
    ;
    ;
    stdlib.protect(ctc2, await interact.informTimeout(), {
      at: './index.rsh:72:35:application',
      fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:91:55:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
      msg: 'informTimeout',
      who: 'p1'
      });
    
    return;
    
    }
  else {
    const {data: [], secs: v396, time: v395, didSend: v98, from: v394 } = txn2;
    const v398 = stdlib.add(v378, v378);
    ;
    let v399 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
    let v400 = v395;
    let v407 = v398;
    
    let txn3 = txn2;
    while (await (async () => {
      const v417 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
      
      return v417;})()) {
      const v424 = stdlib.safeAdd(v400, v379);
      const v428 = stdlib.protect(ctc0, await interact.getHand(), {
        at: './index.rsh:102:44:application',
        fs: ['at ./index.rsh:101:22:application call to [unknown function] (defined at: ./index.rsh:101:26:function exp)'],
        msg: 'getHand',
        who: 'p1'
        });
      const v429 = stdlib.protect(ctc0, await interact.getPrediction(), {
        at: './index.rsh:103:56:application',
        fs: ['at ./index.rsh:101:22:application call to [unknown function] (defined at: ./index.rsh:101:26:function exp)'],
        msg: 'getPrediction',
        who: 'p1'
        });
      const v430 = stdlib.protect(ctc0, await interact.random(), {
        at: 'reach standard library:64:31:application',
        fs: ['at ./index.rsh:104:62:application call to "makeCommitment" (defined at: reach standard library:63:8:function exp)', 'at ./index.rsh:101:22:application call to [unknown function] (defined at: ./index.rsh:101:26:function exp)'],
        msg: 'random',
        who: 'p1'
        });
      const v431 = stdlib.digest([ctc0, ctc0], [v430, v428]);
      const v433 = stdlib.protect(ctc0, await interact.random(), {
        at: 'reach standard library:64:31:application',
        fs: ['at ./index.rsh:105:74:application call to "makeCommitment" (defined at: reach standard library:63:8:function exp)', 'at ./index.rsh:101:22:application call to [unknown function] (defined at: ./index.rsh:101:26:function exp)'],
        msg: 'random',
        who: 'p1'
        });
      const v434 = stdlib.digest([ctc0, ctc0], [v433, v429]);
      
      const txn4 = await (ctc.sendrecv({
        args: [v377, v378, v379, v394, v407, v424, v431, v434],
        evt_cnt: 2,
        funcNum: 4,
        lct: v400,
        onlyIf: true,
        out_tys: [ctc1, ctc1],
        pay: [stdlib.checkedBigNumberify('./index.rsh:111:18:decimal', stdlib.UInt_max, '0'), []],
        sim_p: (async (txn4) => {
          const sim_r = { txns: [], mapRefs: [], maps: [] };
          let sim_txn_ctr = stdlib.UInt_max;
          const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
          
          
          const {data: [v437, v438], secs: v440, time: v439, didSend: v131, from: v436 } = txn4;
          
          ;
          const v448 = stdlib.safeAdd(v439, v379);
          sim_r.isHalt = false;
          
          return sim_r;
          }),
        soloSend: true,
        timeoutAt: ['time', v424],
        tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc0, ctc1, ctc1],
        waitIfNotPresent: false
        }));
      if (txn4.didTimeout) {
        const txn5 = await (ctc.sendrecv({
          args: [v377, v378, v379, v394, v407, v424],
          evt_cnt: 0,
          funcNum: 5,
          lct: v400,
          onlyIf: true,
          out_tys: [],
          pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn5) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [], secs: v530, time: v529, didSend: v261, from: v528 } = txn5;
            
            ;
            sim_r.txns.push({
              kind: 'from',
              to: v394,
              tok: undefined /* Nothing */
              });
            sim_r.txns.push({
              kind: 'halt',
              tok: undefined /* Nothing */
              })
            sim_r.isHalt = true;
            
            return sim_r;
            }),
          soloSend: false,
          timeoutAt: undefined /* mto */,
          tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc0],
          waitIfNotPresent: false
          }));
        const {data: [], secs: v530, time: v529, didSend: v261, from: v528 } = txn5;
        ;
        const v531 = stdlib.addressEq(v377, v528);
        const v532 = stdlib.addressEq(v394, v528);
        const v533 = v531 ? true : v532;
        stdlib.assert(v533, {
          at: 'reach standard library:197:11:dot',
          fs: ['at ./index.rsh:112:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'sender correct',
          who: 'p1'
          });
        ;
        stdlib.protect(ctc2, await interact.informTimeout(), {
          at: './index.rsh:72:35:application',
          fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:112:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'informTimeout',
          who: 'p1'
          });
        
        return;
        
        }
      else {
        const {data: [v437, v438], secs: v440, time: v439, didSend: v131, from: v436 } = txn4;
        ;
        const v441 = stdlib.addressEq(v377, v436);
        stdlib.assert(v441, {
          at: './index.rsh:111:18:dot',
          fs: [],
          msg: 'sender correct',
          who: 'p1'
          });
        const v448 = stdlib.safeAdd(v439, v379);
        const txn5 = await (ctc.recv({
          didSend: false,
          evt_cnt: 2,
          funcNum: 6,
          out_tys: [ctc0, ctc0],
          timeoutAt: ['time', v448],
          waitIfNotPresent: false
          }));
        if (txn5.didTimeout) {
          const txn6 = await (ctc.sendrecv({
            args: [v377, v378, v379, v394, v407, v437, v438, v448],
            evt_cnt: 0,
            funcNum: 7,
            lct: v439,
            onlyIf: true,
            out_tys: [],
            pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn6) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [], secs: v512, time: v511, didSend: v227, from: v510 } = txn6;
              
              ;
              sim_r.txns.push({
                kind: 'from',
                to: v377,
                tok: undefined /* Nothing */
                });
              sim_r.txns.push({
                kind: 'halt',
                tok: undefined /* Nothing */
                })
              sim_r.isHalt = true;
              
              return sim_r;
              }),
            soloSend: false,
            timeoutAt: undefined /* mto */,
            tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc1, ctc1, ctc0],
            waitIfNotPresent: false
            }));
          const {data: [], secs: v512, time: v511, didSend: v227, from: v510 } = txn6;
          ;
          const v513 = stdlib.addressEq(v377, v510);
          const v514 = stdlib.addressEq(v394, v510);
          const v515 = v513 ? true : v514;
          stdlib.assert(v515, {
            at: 'reach standard library:197:11:dot',
            fs: ['at ./index.rsh:124:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'sender correct',
            who: 'p1'
            });
          ;
          stdlib.protect(ctc2, await interact.informTimeout(), {
            at: './index.rsh:72:35:application',
            fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:124:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'informTimeout',
            who: 'p1'
            });
          
          return;
          
          }
        else {
          const {data: [v455, v456], secs: v458, time: v457, didSend: v143, from: v454 } = txn5;
          ;
          const v459 = stdlib.addressEq(v394, v454);
          stdlib.assert(v459, {
            at: './index.rsh:123:18:dot',
            fs: [],
            msg: 'sender correct',
            who: 'p1'
            });
          const v466 = stdlib.safeAdd(v457, v379);
          const txn6 = await (ctc.sendrecv({
            args: [v377, v378, v379, v394, v407, v437, v438, v455, v456, v466, v430, v428, v433, v429],
            evt_cnt: 4,
            funcNum: 8,
            lct: v457,
            onlyIf: true,
            out_tys: [ctc0, ctc0, ctc0, ctc0],
            pay: [stdlib.checkedBigNumberify('./index.rsh:135:18:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn6) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [v471, v472, v473, v474], secs: v476, time: v475, didSend: v155, from: v470 } = txn6;
              
              ;
              const v483 = stdlib.safeAdd(v472, v455);
              const v484 = stdlib.eq(v474, v483);
              const v486 = stdlib.eq(v456, v483);
              const v488 = v486 ? false : true;
              const v489 = v484 ? v488 : false;
              const v491 = v484 ? false : v486;
              const v579 = v491 ? stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '2') : stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
              const v482 = v489 ? stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '0') : v579;
              const cv399 = v482;
              const cv400 = v475;
              const cv407 = v407;
              
              await (async () => {
                const v399 = cv399;
                const v400 = cv400;
                const v407 = cv407;
                
                if (await (async () => {
                  const v417 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
                  
                  return v417;})()) {
                  const v424 = stdlib.safeAdd(v400, v379);
                  sim_r.isHalt = false;
                  }
                else {
                  const v546 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '0'));
                  const v549 = stdlib.safeMul(stdlib.checkedBigNumberify('./index.rsh:148:14:decimal', stdlib.UInt_max, '2'), v378);
                  const v551 = v546 ? v377 : v394;
                  sim_r.txns.push({
                    kind: 'from',
                    to: v551,
                    tok: undefined /* Nothing */
                    });
                  sim_r.txns.push({
                    kind: 'halt',
                    tok: undefined /* Nothing */
                    })
                  sim_r.isHalt = true;
                  }})();
              return sim_r;
              }),
            soloSend: true,
            timeoutAt: ['time', v466],
            tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc1, ctc1, ctc0, ctc0, ctc0, ctc0, ctc0, ctc0, ctc0],
            waitIfNotPresent: false
            }));
          if (txn6.didTimeout) {
            const txn7 = await (ctc.sendrecv({
              args: [v377, v378, v379, v394, v407, v437, v438, v455, v456, v466],
              evt_cnt: 0,
              funcNum: 9,
              lct: v457,
              onlyIf: true,
              out_tys: [],
              pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
              sim_p: (async (txn7) => {
                const sim_r = { txns: [], mapRefs: [], maps: [] };
                let sim_txn_ctr = stdlib.UInt_max;
                const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
                
                
                const {data: [], secs: v494, time: v493, didSend: v193, from: v492 } = txn7;
                
                ;
                sim_r.txns.push({
                  kind: 'from',
                  to: v394,
                  tok: undefined /* Nothing */
                  });
                sim_r.txns.push({
                  kind: 'halt',
                  tok: undefined /* Nothing */
                  })
                sim_r.isHalt = true;
                
                return sim_r;
                }),
              soloSend: false,
              timeoutAt: undefined /* mto */,
              tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc1, ctc1, ctc0, ctc0, ctc0],
              waitIfNotPresent: false
              }));
            const {data: [], secs: v494, time: v493, didSend: v193, from: v492 } = txn7;
            ;
            const v495 = stdlib.addressEq(v377, v492);
            const v496 = stdlib.addressEq(v394, v492);
            const v497 = v495 ? true : v496;
            stdlib.assert(v497, {
              at: 'reach standard library:197:11:dot',
              fs: ['at ./index.rsh:136:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
              msg: 'sender correct',
              who: 'p1'
              });
            ;
            stdlib.protect(ctc2, await interact.informTimeout(), {
              at: './index.rsh:72:35:application',
              fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:136:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
              msg: 'informTimeout',
              who: 'p1'
              });
            
            return;
            
            }
          else {
            const {data: [v471, v472, v473, v474], secs: v476, time: v475, didSend: v155, from: v470 } = txn6;
            ;
            const v477 = stdlib.addressEq(v377, v470);
            stdlib.assert(v477, {
              at: './index.rsh:135:18:dot',
              fs: [],
              msg: 'sender correct',
              who: 'p1'
              });
            const v478 = stdlib.digest([ctc0, ctc0], [v471, v472]);
            const v479 = stdlib.digestEq(v437, v478);
            stdlib.assert(v479, {
              at: 'reach standard library:69:17:application',
              fs: ['at ./index.rsh:139:24:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
              msg: null,
              who: 'p1'
              });
            const v480 = stdlib.digest([ctc0, ctc0], [v473, v474]);
            const v481 = stdlib.digestEq(v438, v480);
            stdlib.assert(v481, {
              at: 'reach standard library:69:17:application',
              fs: ['at ./index.rsh:140:24:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
              msg: null,
              who: 'p1'
              });
            const v483 = stdlib.safeAdd(v472, v455);
            const v484 = stdlib.eq(v474, v483);
            const v486 = stdlib.eq(v456, v483);
            const v488 = v486 ? false : true;
            const v489 = v484 ? v488 : false;
            const v491 = v484 ? false : v486;
            const v579 = v491 ? stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '2') : stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
            const v482 = v489 ? stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '0') : v579;
            const cv399 = v482;
            const cv400 = v475;
            const cv407 = v407;
            
            v399 = cv399;
            v400 = cv400;
            v407 = cv407;
            
            txn3 = txn6;
            continue;}
          
          }
        
        }
      
      }
    const v546 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '0'));
    const v549 = stdlib.safeMul(stdlib.checkedBigNumberify('./index.rsh:148:14:decimal', stdlib.UInt_max, '2'), v378);
    const v551 = v546 ? v377 : v394;
    ;
    stdlib.protect(ctc2, await interact.seeGameOutcome(v399), {
      at: './index.rsh:154:32:application',
      fs: ['at ./index.rsh:152:9:application call to [unknown function] (defined at: ./index.rsh:152:35:function exp)'],
      msg: 'seeGameOutcome',
      who: 'p1'
      });
    
    return;
    }
  
  
  
  };
export async function p2(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for p2 expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for p2 expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Null;
  const ctc2 = stdlib.T_Digest;
  const ctc3 = stdlib.T_Address;
  
  
  const txn1 = await (ctc.recv({
    didSend: false,
    evt_cnt: 2,
    funcNum: 0,
    out_tys: [ctc0, ctc0],
    timeoutAt: undefined /* mto */,
    waitIfNotPresent: false
    }));
  const {data: [v378, v379], secs: v381, time: v380, didSend: v89, from: v377 } = txn1;
  ;
  const v390 = stdlib.safeAdd(v380, v379);
  stdlib.protect(ctc1, await interact.acceptWager(v378), {
    at: './index.rsh:87:29:application',
    fs: ['at ./index.rsh:85:18:application call to [unknown function] (defined at: ./index.rsh:85:22:function exp)'],
    msg: 'acceptWager',
    who: 'p2'
    });
  
  const txn2 = await (ctc.sendrecv({
    args: [v377, v378, v379, v390],
    evt_cnt: 0,
    funcNum: 1,
    lct: v380,
    onlyIf: true,
    out_tys: [],
    pay: [v378, []],
    sim_p: (async (txn2) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [], secs: v396, time: v395, didSend: v98, from: v394 } = txn2;
      
      const v398 = stdlib.add(v378, v378);
      sim_r.txns.push({
        amt: v378,
        kind: 'to',
        tok: undefined /* Nothing */
        });
      const v399 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
      const v400 = v395;
      const v407 = v398;
      
      if (await (async () => {
        const v417 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
        
        return v417;})()) {
        const v424 = stdlib.safeAdd(v400, v379);
        sim_r.isHalt = false;
        }
      else {
        const v546 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '0'));
        const v549 = stdlib.safeMul(stdlib.checkedBigNumberify('./index.rsh:148:14:decimal', stdlib.UInt_max, '2'), v378);
        const v551 = v546 ? v377 : v394;
        sim_r.txns.push({
          kind: 'from',
          to: v551,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        }
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: ['time', v390],
    tys: [ctc3, ctc0, ctc0, ctc0],
    waitIfNotPresent: false
    }));
  if (txn2.didTimeout) {
    const txn3 = await (ctc.sendrecv({
      args: [v377, v378, v379, v390],
      evt_cnt: 0,
      funcNum: 2,
      lct: v380,
      onlyIf: true,
      out_tys: [],
      pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
      sim_p: (async (txn3) => {
        const sim_r = { txns: [], mapRefs: [], maps: [] };
        let sim_txn_ctr = stdlib.UInt_max;
        const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
        
        
        const {data: [], secs: v564, time: v563, didSend: v310, from: v562 } = txn3;
        
        ;
        sim_r.txns.push({
          kind: 'from',
          to: v377,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        
        return sim_r;
        }),
      soloSend: false,
      timeoutAt: undefined /* mto */,
      tys: [ctc3, ctc0, ctc0, ctc0],
      waitIfNotPresent: false
      }));
    const {data: [], secs: v564, time: v563, didSend: v310, from: v562 } = txn3;
    ;
    ;
    stdlib.protect(ctc1, await interact.informTimeout(), {
      at: './index.rsh:72:35:application',
      fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:91:55:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
      msg: 'informTimeout',
      who: 'p2'
      });
    
    return;
    
    }
  else {
    const {data: [], secs: v396, time: v395, didSend: v98, from: v394 } = txn2;
    const v398 = stdlib.add(v378, v378);
    ;
    let v399 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
    let v400 = v395;
    let v407 = v398;
    
    let txn3 = txn2;
    while (await (async () => {
      const v417 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
      
      return v417;})()) {
      const v424 = stdlib.safeAdd(v400, v379);
      const txn4 = await (ctc.recv({
        didSend: false,
        evt_cnt: 2,
        funcNum: 4,
        out_tys: [ctc2, ctc2],
        timeoutAt: ['time', v424],
        waitIfNotPresent: false
        }));
      if (txn4.didTimeout) {
        const txn5 = await (ctc.sendrecv({
          args: [v377, v378, v379, v394, v407, v424],
          evt_cnt: 0,
          funcNum: 5,
          lct: v400,
          onlyIf: true,
          out_tys: [],
          pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn5) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [], secs: v530, time: v529, didSend: v261, from: v528 } = txn5;
            
            ;
            sim_r.txns.push({
              kind: 'from',
              to: v394,
              tok: undefined /* Nothing */
              });
            sim_r.txns.push({
              kind: 'halt',
              tok: undefined /* Nothing */
              })
            sim_r.isHalt = true;
            
            return sim_r;
            }),
          soloSend: false,
          timeoutAt: undefined /* mto */,
          tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc0],
          waitIfNotPresent: false
          }));
        const {data: [], secs: v530, time: v529, didSend: v261, from: v528 } = txn5;
        ;
        const v531 = stdlib.addressEq(v377, v528);
        const v532 = stdlib.addressEq(v394, v528);
        const v533 = v531 ? true : v532;
        stdlib.assert(v533, {
          at: 'reach standard library:197:11:dot',
          fs: ['at ./index.rsh:112:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'sender correct',
          who: 'p2'
          });
        ;
        stdlib.protect(ctc1, await interact.informTimeout(), {
          at: './index.rsh:72:35:application',
          fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:112:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'informTimeout',
          who: 'p2'
          });
        
        return;
        
        }
      else {
        const {data: [v437, v438], secs: v440, time: v439, didSend: v131, from: v436 } = txn4;
        ;
        const v441 = stdlib.addressEq(v377, v436);
        stdlib.assert(v441, {
          at: './index.rsh:111:18:dot',
          fs: [],
          msg: 'sender correct',
          who: 'p2'
          });
        const v448 = stdlib.safeAdd(v439, v379);
        const v452 = stdlib.protect(ctc0, await interact.getHand(), {
          at: './index.rsh:119:54:application',
          fs: ['at ./index.rsh:118:22:application call to [unknown function] (defined at: ./index.rsh:118:25:function exp)'],
          msg: 'getHand',
          who: 'p2'
          });
        const v453 = stdlib.protect(ctc0, await interact.getPrediction(), {
          at: './index.rsh:120:66:application',
          fs: ['at ./index.rsh:118:22:application call to [unknown function] (defined at: ./index.rsh:118:25:function exp)'],
          msg: 'getPrediction',
          who: 'p2'
          });
        
        const txn5 = await (ctc.sendrecv({
          args: [v377, v378, v379, v394, v407, v437, v438, v448, v452, v453],
          evt_cnt: 2,
          funcNum: 6,
          lct: v439,
          onlyIf: true,
          out_tys: [ctc0, ctc0],
          pay: [stdlib.checkedBigNumberify('./index.rsh:123:18:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn5) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [v455, v456], secs: v458, time: v457, didSend: v143, from: v454 } = txn5;
            
            ;
            const v466 = stdlib.safeAdd(v457, v379);
            sim_r.isHalt = false;
            
            return sim_r;
            }),
          soloSend: true,
          timeoutAt: ['time', v448],
          tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc2, ctc2, ctc0, ctc0, ctc0],
          waitIfNotPresent: false
          }));
        if (txn5.didTimeout) {
          const txn6 = await (ctc.sendrecv({
            args: [v377, v378, v379, v394, v407, v437, v438, v448],
            evt_cnt: 0,
            funcNum: 7,
            lct: v439,
            onlyIf: true,
            out_tys: [],
            pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn6) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [], secs: v512, time: v511, didSend: v227, from: v510 } = txn6;
              
              ;
              sim_r.txns.push({
                kind: 'from',
                to: v377,
                tok: undefined /* Nothing */
                });
              sim_r.txns.push({
                kind: 'halt',
                tok: undefined /* Nothing */
                })
              sim_r.isHalt = true;
              
              return sim_r;
              }),
            soloSend: false,
            timeoutAt: undefined /* mto */,
            tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc2, ctc2, ctc0],
            waitIfNotPresent: false
            }));
          const {data: [], secs: v512, time: v511, didSend: v227, from: v510 } = txn6;
          ;
          const v513 = stdlib.addressEq(v377, v510);
          const v514 = stdlib.addressEq(v394, v510);
          const v515 = v513 ? true : v514;
          stdlib.assert(v515, {
            at: 'reach standard library:197:11:dot',
            fs: ['at ./index.rsh:124:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'sender correct',
            who: 'p2'
            });
          ;
          stdlib.protect(ctc1, await interact.informTimeout(), {
            at: './index.rsh:72:35:application',
            fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:124:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'informTimeout',
            who: 'p2'
            });
          
          return;
          
          }
        else {
          const {data: [v455, v456], secs: v458, time: v457, didSend: v143, from: v454 } = txn5;
          ;
          const v459 = stdlib.addressEq(v394, v454);
          stdlib.assert(v459, {
            at: './index.rsh:123:18:dot',
            fs: [],
            msg: 'sender correct',
            who: 'p2'
            });
          const v466 = stdlib.safeAdd(v457, v379);
          const txn6 = await (ctc.recv({
            didSend: false,
            evt_cnt: 4,
            funcNum: 8,
            out_tys: [ctc0, ctc0, ctc0, ctc0],
            timeoutAt: ['time', v466],
            waitIfNotPresent: false
            }));
          if (txn6.didTimeout) {
            const txn7 = await (ctc.sendrecv({
              args: [v377, v378, v379, v394, v407, v437, v438, v455, v456, v466],
              evt_cnt: 0,
              funcNum: 9,
              lct: v457,
              onlyIf: true,
              out_tys: [],
              pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
              sim_p: (async (txn7) => {
                const sim_r = { txns: [], mapRefs: [], maps: [] };
                let sim_txn_ctr = stdlib.UInt_max;
                const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
                
                
                const {data: [], secs: v494, time: v493, didSend: v193, from: v492 } = txn7;
                
                ;
                sim_r.txns.push({
                  kind: 'from',
                  to: v394,
                  tok: undefined /* Nothing */
                  });
                sim_r.txns.push({
                  kind: 'halt',
                  tok: undefined /* Nothing */
                  })
                sim_r.isHalt = true;
                
                return sim_r;
                }),
              soloSend: false,
              timeoutAt: undefined /* mto */,
              tys: [ctc3, ctc0, ctc0, ctc3, ctc0, ctc2, ctc2, ctc0, ctc0, ctc0],
              waitIfNotPresent: false
              }));
            const {data: [], secs: v494, time: v493, didSend: v193, from: v492 } = txn7;
            ;
            const v495 = stdlib.addressEq(v377, v492);
            const v496 = stdlib.addressEq(v394, v492);
            const v497 = v495 ? true : v496;
            stdlib.assert(v497, {
              at: 'reach standard library:197:11:dot',
              fs: ['at ./index.rsh:136:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
              msg: 'sender correct',
              who: 'p2'
              });
            ;
            stdlib.protect(ctc1, await interact.informTimeout(), {
              at: './index.rsh:72:35:application',
              fs: ['at ./index.rsh:71:13:application call to [unknown function] (defined at: ./index.rsh:71:39:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:70:30:function exp)', 'at ./index.rsh:136:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
              msg: 'informTimeout',
              who: 'p2'
              });
            
            return;
            
            }
          else {
            const {data: [v471, v472, v473, v474], secs: v476, time: v475, didSend: v155, from: v470 } = txn6;
            ;
            const v477 = stdlib.addressEq(v377, v470);
            stdlib.assert(v477, {
              at: './index.rsh:135:18:dot',
              fs: [],
              msg: 'sender correct',
              who: 'p2'
              });
            const v478 = stdlib.digest([ctc0, ctc0], [v471, v472]);
            const v479 = stdlib.digestEq(v437, v478);
            stdlib.assert(v479, {
              at: 'reach standard library:69:17:application',
              fs: ['at ./index.rsh:139:24:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
              msg: null,
              who: 'p2'
              });
            const v480 = stdlib.digest([ctc0, ctc0], [v473, v474]);
            const v481 = stdlib.digestEq(v438, v480);
            stdlib.assert(v481, {
              at: 'reach standard library:69:17:application',
              fs: ['at ./index.rsh:140:24:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
              msg: null,
              who: 'p2'
              });
            const v483 = stdlib.safeAdd(v472, v455);
            const v484 = stdlib.eq(v474, v483);
            const v486 = stdlib.eq(v456, v483);
            const v488 = v486 ? false : true;
            const v489 = v484 ? v488 : false;
            const v491 = v484 ? false : v486;
            const v579 = v491 ? stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '2') : stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
            const v482 = v489 ? stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '0') : v579;
            const cv399 = v482;
            const cv400 = v475;
            const cv407 = v407;
            
            v399 = cv399;
            v400 = cv400;
            v407 = cv407;
            
            txn3 = txn6;
            continue;}
          
          }
        
        }
      
      }
    const v546 = stdlib.eq(v399, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '0'));
    const v549 = stdlib.safeMul(stdlib.checkedBigNumberify('./index.rsh:148:14:decimal', stdlib.UInt_max, '2'), v378);
    const v551 = v546 ? v377 : v394;
    ;
    stdlib.protect(ctc1, await interact.seeGameOutcome(v399), {
      at: './index.rsh:154:32:application',
      fs: ['at ./index.rsh:152:9:application call to [unknown function] (defined at: ./index.rsh:152:35:function exp)'],
      msg: 'seeGameOutcome',
      who: 'p2'
      });
    
    return;
    }
  
  
  
  };
const _ALGO = {
  ABI: {
    impure: [],
    pure: [],
    sigs: []
    },
  appApproval: `ByAOAAFQCAUJIAcoApgBqAFYMCYDAQABAQAiNQAxGEEE9ypkSSJbNQElWzUCNhoAF0lBAAciNQQjNQYANhoCFzUENhoDNhoBF0khBAxAAoRJIQcMQAF4SSUMQAEfSSEFDEAAViEFEkQhBTQBEkQ0BEkiEkw0AhIRRChkKWRQSTUDVzAgNf+ABKIFZo6wMgY0AyELWw9ENANXACAxABI0/zEAEhFEsSKyATQDJFuyCCOyEDT/sgezQgQPSCEFNAESRDQESSISTDQCEhFEKGQpZFBJNQNXACA1/0k1BUlKIls1/iVbNf2BEFs1/IEYWzX7gAR/ojtSNP4WUDT9FlA0/BZQNPsWULAyBjQDIQtbDEQ0/zEAEkQ0A1dYIDT+FjT9FlABEkQ0A1d4IDT8FjT7FlABEkQ0/TQDIQpbCDX6NPs0+hI1+TQDgaABWzT6EjX4NP80AyEGWzQDIQhbNANXMCAjIQk0+RQ0+BBNIjT5NPgUEE0yBjQDJFtCAuxIIQc0ARJENARJIhJMNAISEUQoZClkUEk1A1cAIDX/gATiG7OpsDIGNAMhClsPRDT/MQASNANXMCAxABIRRLEisgE0AyRbsggjshA0/7IHs0IC+kmBBgxAAK5IIQc0ARJENARJIhJMNAISEUQoZClkUEk1A0lKSklXACA1/yEGWzX+IQhbNf1XMCA1/CRbNftXWCA1+ld4IDX5STUFSSJbNfglWzX3gARKIcv8NPgWUDT3FlCwMgY0AyEKWwxENPwxABJEMgY0/Qg19jT/NP4WUDT9FlA0/FA0+xZQNPpQNPlQNPgWUDT3FlA09hZQKEsBVwB/ZylLAVd/MWdIIQU1ATIGNQJCAmFIIQQ0ARJENARJIhJMNAISEUQoZEk1A1cwIDX/gATMmZJcsDIGNAMhDFsPRDQDVwAgMQASNP8xABIRRLEisgE0AyRbsggjshA0/7IHs0IB9UkhCQxAAOBJgQQMQACYSCEENAESRDQESSISTDQCEhFEKGRJNQNJSklXACA1/yEGWzX+IQhbNf1XMCA1/CRbNftJNQVJVwAgNfpXICA1+YAEYF2kKzT6UDT5ULAyBjQDIQxbDEQ0/zEAEkQyBjT9CDX4NP80/hZQNP0WUDT8UDT7FlA0+lA0+VA0+BZQKEsBVwB/ZylLAVd/IWdIIQc1ATIGNQJCAWshCRJEIzQBEkQ0BEkiEkw0AhIRRChkNQOABEGxQE2wMgY0AyENWw9EsSKyATQDIQZbsggjshA0A1cAILIHs0IBDkkjDEAASEgjNAESRDQESSISTDQCEhFEKGRJNQMhBls1/4AEmouRdLAyBjQDIQ1bDEQ0/4gBRjQDVwAgNP80AyEIWzEAIzIGNP9JCEIAX0iBoI0GiAEmIjQBEkQ0BEkiEkw0AhIRREk1BUkiWzX/JVs1/oAErNEfwzT/FlA0/hZQsDT/iAD2MgY0/gg1/TEANP8WUDT+FlA0/RZQKEsBVwA4Z0gjNQEyBjUCQgB9Nf81/jX9Nfw1+zX6Nfk0/SMSQQAvNP40+wg1+DT5NPoWUDT7FlA0/FA0/xZQNPgWUChLAVcAYGdIIQQ1ATIGNQJCADmxIrIBIQk0+guyCCOyEDT8NPk0/SISTbIHs0IAADEZIQQSRLEisgEisggjshAyCbIJMgqyB7NCAAUxGSISRCo0ARY0AhZQZzQGQQAKgAQVH3x1NAdQsDQASSMIMgQSRDEWEkQjQzEZIhJEQv/fIjE0EkSBAzE1EkQiMTYSRCIxNxJEIjUBIjUCQv+uNABJSiMINQA4BzIKEkQ4ECMSRDgIEkSJ`,
  appClear: `Bw==`,
  companionInfo: null,
  extraPages: 0,
  mapDataKeys: 0,
  mapDataSize: 0,
  stateKeys: 2,
  stateSize: 176,
  unsupported: [],
  version: 11,
  warnings: []
  };
const _ETH = {
  ABI: `[
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v378",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v379",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "stateMutability": "payable",
    "type": "constructor"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "msg",
        "type": "uint256"
      }
    ],
    "name": "ReachError",
    "type": "error"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v378",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v379",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e0",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e1",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e2",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v437",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v438",
                "type": "uint256"
              }
            ],
            "internalType": "struct T10",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T11",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e4",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e5",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v455",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v456",
                "type": "uint256"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e6",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e7",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v471",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v472",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v473",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v474",
                "type": "uint256"
              }
            ],
            "internalType": "struct T15",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T16",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e8",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e9",
    "type": "event"
  },
  {
    "stateMutability": "payable",
    "type": "fallback"
  },
  {
    "inputs": [],
    "name": "_reachCreationTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentState",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      },
      {
        "internalType": "bytes",
        "name": "",
        "type": "bytes"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m1",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m2",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v437",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v438",
                "type": "uint256"
              }
            ],
            "internalType": "struct T10",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T11",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m4",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m5",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v455",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v456",
                "type": "uint256"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m6",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m7",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v471",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v472",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v473",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v474",
                "type": "uint256"
              }
            ],
            "internalType": "struct T15",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T16",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m8",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m9",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "stateMutability": "payable",
    "type": "receive"
  }
]`,
  Bytecode: `0x608060405260405162001de138038062001de18339810160408190526200002691620002a9565b6000808055436003556040805160208082018352928152815133815284518185015284840151805182850152909301516060840152905190917fa736757a943474ef5983bb0422ab3a1e64bcd39e99635f4430c7765118231f95919081900360800190a16020820151516200009f90341460076200014a565b620000b9438360200151602001516200017560201b60201c565b81526040805160808082018352600060208084018281528486018381526060808701858152338089528b860180515186525186015184528a5182526001968790554390965588518086019690965292518589015290519084015251828401528451808303909301835260a090910190935280519192620001409260029290910190620001cc565b505050506200036d565b81620001715760405163100960cb60e01b8152600481018290526024015b60405180910390fd5b5050565b60008262000184838262000309565b9150811015620001c65760405162461bcd60e51b815260206004820152600c60248201526b616464206f766572666c6f7760a01b604482015260640162000168565b92915050565b828054620001da9062000330565b90600052602060002090601f016020900481019282620001fe576000855562000249565b82601f106200021957805160ff191683800117855562000249565b8280016001018555821562000249579182015b82811115620002495782518255916020019190600101906200022c565b50620002579291506200025b565b5090565b5b808211156200025757600081556001016200025c565b604080519081016001600160401b0381118282101715620002a357634e487b7160e01b600052604160045260246000fd5b60405290565b60008183036060811215620002bd57600080fd5b620002c762000272565b835181526040601f1983011215620002de57600080fd5b620002e862000272565b60208581015182526040909501518582015293810193909352509092915050565b600082198211156200032b57634e487b7160e01b600052601160045260246000fd5b500190565b600181811c908216806200034557607f821691505b602082108114156200036757634e487b7160e01b600052602260045260246000fd5b50919050565b611a64806200037d6000396000f3fe60806040526004361061009a5760003560e01c80638e314769116100615780638e31476914610115578063ab53f2c614610128578063bf2c5b241461014b578063cc923b291461015e578063de73699814610171578063ebdbfdcc1461018457005b80631e93b0f1146100a357806321642639146100c75780632c10a159146100da5780637eea518c146100ed578063832307571461010057005b366100a157005b005b3480156100af57600080fd5b506003545b6040519081526020015b60405180910390f35b6100a16100d536600461154f565b610197565b6100a16100e8366004611572565b6103fc565b6100a16100fb366004611572565b61058b565b34801561010c57600080fd5b506001546100b4565b6100a1610123366004611572565b610709565b34801561013457600080fd5b5061013d6108a4565b6040516100be929190611584565b6100a1610159366004611572565b610941565b6100a161016c3660046115e1565b610ad8565b6100a161017f366004611572565b610ddf565b6100a161019236600461154f565b610f3a565b6101a7600760005414601c6111ab565b6101c1813515806101ba57506001548235145b601d6111ab565b6000808055600280546101d3906115f3565b80601f01602080910402602001604051908101604052809291908181526020018280546101ff906115f3565b801561024c5780601f106102215761010080835404028352916020019161024c565b820191906000526020600020905b81548152906001019060200180831161022f57829003601f168201915b5050505050806020019051810190610264919061167c565b905061027c6040518060200160405280600081525090565b61028d8260e001514310601e6111ab565b7fb2a03f9306ab783007397921312164b54fbeead1388356342ff3ef55c8552b3f33846040516102be929190611728565b60405180910390a16102d23415601a6111ab565b60608201516102ed906001600160a01b03163314601b6111ab565b6102fb4383604001516111d1565b81526040805161014081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c0810182905260e08101829052610100810182905261012081019190915282516001600160a01b0390811682526020808501518184015260408086015181850152606080870151909316928401929092526080808601519084015260a0808601519084015260c080860151908401528581013560e084015285820135610100840152835161012084015260096000554360015590516103d191839101611759565b604051602081830303815290604052600290805190602001906103f5929190611408565b5050505050565b61040c60016000541460096111ab565b6104268135158061041f57506001548235145b600a6111ab565b600080805560028054610438906115f3565b80601f0160208091040260200160405190810160405280929190818152602001828054610464906115f3565b80156104b15780601f10610486576101008083540402835291602001916104b1565b820191906000526020600020905b81548152906001019060200180831161049457829003601f168201915b50505050508060200190518101906104c991906117e0565b90506104dc81606001514310600b6111ab565b7f400d21ea4e4a5e28b4ae5f0f476c201fc8036473fcf7c8cd252f38698020b4f1338360405161050d929190611859565b60405180910390a16105268160200151341460086111ab565b61052e61148c565b815181516001600160a01b039091169052602080830180518351830152604080850151845190910152825133606090910152818301805160019052514392019190915251800160208201516040015261058681611224565b505050565b61059b600160005414600d6111ab565b6105b5813515806105ae57506001548235145b600e6111ab565b6000808055600280546105c7906115f3565b80601f01602080910402602001604051908101604052809291908181526020018280546105f3906115f3565b80156106405780601f1061061557610100808354040283529160200191610640565b820191906000526020600020905b81548152906001019060200180831161062357829003601f168201915b505050505080602001905181019061065891906117e0565b905061066c8160600151431015600f6111ab565b7f919263be6d51bec670ce110fb6a7df03fe323e3de4dade5355bccc6a4b06d950338360405161069d929190611859565b60405180910390a16106b13415600c6111ab565b805160208201516040516001600160a01b039092169181156108fc0291906000818181858888f193505050501580156106ee573d6000803e3d6000fd5b5060008080556001819055610705906002906114e5565b5050565b61071960056000541460176111ab565b6107338135158061072c57506001548235145b60186111ab565b600080805560028054610745906115f3565b80601f0160208091040260200160405190810160405280929190818152602001828054610771906115f3565b80156107be5780601f10610793576101008083540402835291602001916107be565b820191906000526020600020905b8154815290600101906020018083116107a157829003601f168201915b50505050508060200190518101906107d69190611896565b90506107ea8160a0015143101560196111ab565b7fbe731e9f2a129299a212b8ec3ac324fa99671cd00a5a827cbd3d4fe6d7ad541d338360405161081b929190611859565b60405180910390a161082f341560156111ab565b8051610863906001600160a01b031633146108595760608201516001600160a01b0316331461085c565b60015b60166111ab565b80606001516001600160a01b03166108fc82608001519081150290604051600060405180830381858888f193505050501580156106ee573d6000803e3d6000fd5b6000606060005460028080546108b9906115f3565b80601f01602080910402602001604051908101604052809291908181526020018280546108e5906115f3565b80156109325780601f1061090757610100808354040283529160200191610932565b820191906000526020600020905b81548152906001019060200180831161091557829003601f168201915b50505050509050915091509091565b61095160076000541460216111ab565b61096b8135158061096457506001548235145b60226111ab565b60008080556002805461097d906115f3565b80601f01602080910402602001604051908101604052809291908181526020018280546109a9906115f3565b80156109f65780601f106109cb576101008083540402835291602001916109f6565b820191906000526020600020905b8154815290600101906020018083116109d957829003601f168201915b5050505050806020019051810190610a0e919061167c565b9050610a228160e0015143101560236111ab565b7f3a35e33c7cbe4475e726117e3691b4a75ad6c9b28c29c59a1ef792dd449861bb3383604051610a53929190611859565b60405180910390a1610a673415601f6111ab565b8051610a9b906001600160a01b03163314610a915760608201516001600160a01b03163314610a94565b60015b60206111ab565b805160808201516040516001600160a01b039092169181156108fc0291906000818181858888f193505050501580156106ee573d6000803e3d6000fd5b610ae860096000541460286111ab565b610b0281351580610afb57506001548235145b60296111ab565b600080805560028054610b14906115f3565b80601f0160208091040260200160405190810160405280929190818152602001828054610b40906115f3565b8015610b8d5780601f10610b6257610100808354040283529160200191610b8d565b820191906000526020600020905b815481529060010190602001808311610b7057829003601f168201915b5050505050806020019051810190610ba5919061192a565b6040805160608101825260008082526020820181905291810191909152909150610bd78261012001514310602a6111ab565b604080513381528435602080830191909152850135818301529084013560608083019190915284013560808083019190915284013560a08201527fc7e07aa759791812e0e03fb583c5fbed2f43e8adb4535b4faa695e77e84ea4fe9060c00160405180910390a1610c4a341560246111ab565b8151610c62906001600160a01b0316331460256111ab565b60408051610cae91610c8891602080880135928801359101918252602082015260400190565b6040516020818303038152906040528051906020012060001c8360a001511460266111ab565b604080516060858101356020830152608086013592820192909252610cf491016040516020818303038152906040528051906020012060001c8360c001511460276111ab565b610d0983602001602001358360e001516111d1565b808252608084013581146020830152610100830151146040820152610d2c61148c565b825181516001600160a01b039182169052602080850151835182015260408086015184519091015260608086015184519316920191909152820151610d72576000610d85565b8160400151610d82576001610d85565b60005b610db1578160200151610d9c578160400151610d9f565b60005b610daa576001610db4565b6002610db4565b60005b60208083018051929092528151439101526080840151905160400152610dd981611224565b50505050565b610def600960005414602d6111ab565b610e0981351580610e0257506001548235145b602e6111ab565b600080805560028054610e1b906115f3565b80601f0160208091040260200160405190810160405280929190818152602001828054610e47906115f3565b8015610e945780601f10610e6957610100808354040283529160200191610e94565b820191906000526020600020905b815481529060010190602001808311610e7757829003601f168201915b5050505050806020019051810190610eac919061192a565b9050610ec1816101200151431015602f6111ab565b7f7533cfcbaea81c55f5c15df7ca9474738a32835ebe63ae177376e624bc7df0bd3383604051610ef2929190611859565b60405180910390a1610f063415602b6111ab565b8051610863906001600160a01b03163314610f305760608201516001600160a01b03163314610f33565b60015b602c6111ab565b610f4a60056000541460126111ab565b610f6481351580610f5d57506001548235145b60136111ab565b600080805560028054610f76906115f3565b80601f0160208091040260200160405190810160405280929190818152602001828054610fa2906115f3565b8015610fef5780601f10610fc457610100808354040283529160200191610fef565b820191906000526020600020905b815481529060010190602001808311610fd257829003601f168201915b50505050508060200190518101906110079190611896565b905061101f6040518060200160405280600081525090565b6110308260a00151431060146111ab565b7fa8815bd11c35a4f9905db53f65c359036789c5fd334917c999c5b2420107265a3384604051611061929190611728565b60405180910390a1611075341560106111ab565b815161108d906001600160a01b0316331460116111ab565b61109b4383604001516111d1565b81526040805161010081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c0810182905260e081019190915282516001600160a01b039081168252602080850151818401526040808601518185015260608087015190931692840192909252608080860151908401528581013560a08401528582013560c0840152835160e084015260076000554360015590516103d19183910160006101008201905060018060a01b038084511683526020840151602084015260408401516040840152806060850151166060840152506080830151608083015260a083015160a083015260c083015160c083015260e083015160e083015292915050565b816107055760405163100960cb60e01b8152600481018290526024015b60405180910390fd5b6000826111de83826119d5565b915081101561121e5760405162461bcd60e51b815260206004820152600c60248201526b616464206f766572666c6f7760a01b60448201526064016111c8565b92915050565b604080516020810190915260008152602082015151600114156113485761125b8260200151602001518360000151604001516111d1565b81526040805160c081018252600080825260208201819052918101829052606081018290526080810182905260a08101919091528251516001600160a01b039081168083528451602090810151818501908152865160409081015181870190815288516060908101518716818901908152858b01518401516080808b019182528b5160a0808d019182526005600055436001558751998a019a909a529651958801959095529251918601919091525190951690830152925191810191909152905160c082015260e00160405160208183030381529060405260029080519060200190610dd9929190611408565b6020820151511561135e57815160600151611362565b8151515b6001600160a01b03166108fc61138160028560000151602001516113a9565b6040518115909202916000818181858888f193505050501580156106ee573d6000803e3d6000fd5b60008115806113cd575082826113bf81836119ed565b92506113cb9083611a0c565b145b61121e5760405162461bcd60e51b815260206004820152600c60248201526b6d756c206f766572666c6f7760a01b60448201526064016111c8565b828054611414906115f3565b90600052602060002090601f016020900481019282611436576000855561147c565b82601f1061144f57805160ff191683800117855561147c565b8280016001018555821561147c579182015b8281111561147c578251825591602001919060010190611461565b50611488929150611522565b5090565b6040805160c0810182526000918101828152606082018390526080820183905260a082019290925290819081526020016114e060405180606001604052806000815260200160008152602001600081525090565b905290565b5080546114f1906115f3565b6000825580601f10611501575050565b601f01602090049060005260206000209081019061151f9190611522565b50565b5b808211156114885760008155600101611523565b60006060828403121561154957600080fd5b50919050565b60006060828403121561156157600080fd5b61156b8383611537565b9392505050565b60006040828403121561154957600080fd5b82815260006020604081840152835180604085015260005b818110156115b85785810183015185820160600152820161159c565b818111156115ca576000606083870101525b50601f01601f191692909201606001949350505050565b600060a0828403121561154957600080fd5b600181811c9082168061160757607f821691505b6020821081141561154957634e487b7160e01b600052602260045260246000fd5b604051610140810167ffffffffffffffff8111828210171561165a57634e487b7160e01b600052604160045260246000fd5b60405290565b80516001600160a01b038116811461167757600080fd5b919050565b600061010080838503121561169057600080fd5b6040519081019067ffffffffffffffff821181831017156116c157634e487b7160e01b600052604160045260246000fd5b816040526116ce84611660565b815260208401516020820152604084015160408201526116f060608501611660565b60608201526080840151608082015260a084015160a082015260c084015160c082015260e084015160e0820152809250505092915050565b6001600160a01b03831681526080810161156b60208301848035825260208082013590830152604090810135910152565b81516001600160a01b0316815261014081016020830151602083015260408301516040830152606083015161179960608401826001600160a01b03169052565b506080830151608083015260a083015160a083015260c083015160c083015260e083015160e083015261010080840151818401525061012080840151818401525092915050565b6000608082840312156117f257600080fd5b6040516080810181811067ffffffffffffffff8211171561182357634e487b7160e01b600052604160045260246000fd5b60405261182f83611660565b81526020830151602082015260408301516040820152606083015160608201528091505092915050565b6001600160a01b03831681528135602080830191909152606082019083013580151580821461188757600080fd5b80604085015250509392505050565b600060c082840312156118a857600080fd5b60405160c0810181811067ffffffffffffffff821117156118d957634e487b7160e01b600052604160045260246000fd5b6040526118e583611660565b8152602083015160208201526040830151604082015261190760608401611660565b60608201526080830151608082015260a083015160a08201528091505092915050565b6000610140828403121561193d57600080fd5b611945611628565b61194e83611660565b8152602083015160208201526040830151604082015261197060608401611660565b60608201526080830151608082015260a083015160a082015260c083015160c082015260e083015160e08201526101008084015181830152506101208084015181830152508091505092915050565b634e487b7160e01b600052601160045260246000fd5b600082198211156119e8576119e86119bf565b500190565b6000816000190483118215151615611a0757611a076119bf565b500290565b600082611a2957634e487b7160e01b600052601260045260246000fd5b50049056fea2646970667358221220072e9e4c38b588bb3c0a477ad6d2346d43fb7f9901a17828a016590b2d0df28064736f6c634300080c0033`,
  BytecodeLen: 7649,
  Which: `oD`,
  version: 8,
  views: {
    }
  };
export const _stateSourceMap = {
  1: {
    at: './index.rsh:83:13:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  2: {
    at: 'reach standard library:199:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:91:55:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  4: {
    at: './index.rsh:150:13:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  5: {
    at: './index.rsh:99:17:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  6: {
    at: 'reach standard library:199:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:112:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  7: {
    at: './index.rsh:114:17:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  8: {
    at: 'reach standard library:199:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:124:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  9: {
    at: './index.rsh:125:17:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  10: {
    at: 'reach standard library:199:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:136:59:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
    msg: null,
    who: 'Module'
    }
  };
export const _Connectors = {
  ALGO: _ALGO,
  ETH: _ETH
  };
export const _Participants = {
  "p1": p1,
  "p2": p2
  };
export const _APIs = {
  };
