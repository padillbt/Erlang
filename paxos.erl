-module(paxos).
-export([start_synod_member/1,
         generate_unused_ballot_number/1,
         disable_member/1,
         enable_member/1,
         send_nextballot/2,
         send_beginballot/3,
         send_success/2,
         set_members/2,
         start_propose_value/2,
         send_fake_lastvote/5,
         get_proposal_state/1,
         send_fake_voted/3,
         propose_value/2,
         start_paxos_member/1,
         get_proposal_state/2,
         start_propose_value/3,
         propose_value/3,
         end_paxos_member/1,
         start_paxos_monitor/0,
         create_monitored_member/3]).
-include_lib("eunit/include/eunit.hrl").
 
 
%% In this assignment, we're going to be implmenting the Paxos
%% algorythm - a famous distributed consensious reaching algorithm.
%%
 
%% We're going to start by implementing the "meat" of the overall
%% system - the synod algorythm.  Then we'll move on to add additional
%% feaures and make things robust.
%%
%% The algorithm itself has a wide variety of web resources, many of
%% them confusing.  In terms just the Synod algorithm, I personally
%% recommend two resources:
 
% https://distributedthoughts.wordpress.com/2013/09/30/understanding-paxos-part-2/
% http://research.microsoft.com/en-us/um/people/lamport/pubs/lamport-paxos.pdf
% (Section 2, in particular section 2.2)
 
%% You can implement the details of the protcol any way you wish, but
%% to facilitate my testing you must implement a few key functions.
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PART 1: Synod Member (25 Points)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
            
 
% This creates a synod member process that can be used for subsequent
% calls.
%
% The UniqueId is an atom (e.g. synod1) and when you create the member
% you should register it under that atom using prolog's facility
% registered processes:
% http://www.erlang.org/doc/reference_manual/processes.html
send_with_timeout(UniqueId, Message) ->
  Pid = whereis(UniqueId),
  Pid ! erlang:append_element(Message, self()),
  receive
    ReturnValue -> ReturnValue
  after
    50 -> ignored
  end.

heartbeat({Id}, Server) ->
  put(server, Server),
  put(name, Id),
  receive
    Request -> Request
  end,
  if
	(Request == exit) -> Server = get(server), Id = get(name), exit({Id, Server})
  end,
  NewState = getNextState({Id}, Request),
  heartbeat(NewState).
 
heartbeat(State) ->
  receive
    Request -> Request
  end,
  NewState = getNextState(State, Request),
  heartbeat(NewState).
 
getNextState({disabled, State}, enable) -> State;
getNextState({disabled, State}, _) -> {disabled, State};
getNextState(State, disable) -> {disabled, State};
getNextState({UniqueId}, Request) ->
  getNextState({UniqueId, {1, UniqueId}}, Request);
 
getNextState({UniqueId, {BallotNumber, BallotId}}, {genballot, ReturnPid}) ->
  ReturnPid ! {BallotNumber, BallotId},
  {UniqueId, {BallotNumber, BallotId}};
 
getNextState({UniqueId, {BallotNumber, BallotId}}, {nextballot, {NewNumber, _}, ReturnPid}) when BallotNumber > NewNumber ->
  ReturnPid ! ignored,
  {UniqueId, {BallotNumber, BallotId}};
getNextState({UniqueId, {_, _}}, {nextballot, Ballot, ReturnPid}) ->
  ReturnPid ! {lastvote, UniqueId, null, null, Ballot},
  {UniqueId, Ballot};
 
getNextState({UniqueId, {BallotNumber, BallotId}}, {beginballot, {NewNumber, _}, _, ReturnPid}) when BallotNumber > NewNumber ->
  ReturnPid ! ignored,
  {UniqueId, {BallotNumber, BallotId}};
getNextState({UniqueId, {_, _}}, {beginballot, Ballot, Value, ReturnPid}) ->
  ReturnPid ! {voted, UniqueId, Ballot},
  {UniqueId, {Ballot, Value}, Ballot, []};
 
getNextState({UniqueId, {BallotNumber, BallotId}}, {setmembers, SynodIds, ReturnPid}) ->
  ReturnPid ! ok,
  put(synod_ids, SynodIds),
  {UniqueId, {BallotNumber, BallotId}};
 
getNextState({UniqueId, Ballot}, {proposevalue, Value}) ->
  SynodIds = get(synod_ids),
  lists:foreach(fun(Id) ->
        Pid = whereis(Id),
        Pid ! {nextballot, Ballot, self()}
    end, SynodIds),
  put(proposal_state, next),
  put(quorum_timer, now()),
  {UniqueId, {null, Value}, Ballot, []};

getNextState({UniqueId, Ballot}, {proposevalue, Key, Value}) ->
  SynodIds = get(synod_ids),
  put(Key, Value),
  lists:foreach(fun(Id) ->
        Pid = whereis(Id),
        Pid ! {nextballot, Ballot, self()}
    end, SynodIds),
  put(proposal_state, next),
  put(quorum_timer, now()),
  {UniqueId, {null, Value}, Ballot, []};
 
getNextState({UniqueId, LastVote, {Number, Id}, WaitingFor}, {genballot, ReturnPid}) ->
  NextBallot = {Number + 1, UniqueId},
  ReturnPid ! NextBallot,
  {UniqueId, LastVote, {Number, Id}, WaitingFor};
 
getNextState({UniqueId, LastVote, CurrentBallot, WaitingFor}, {nextballot, Ballot, ReturnPid}) when CurrentBallot > Ballot ->
  ReturnPid ! ignored,
  {UniqueId, LastVote, CurrentBallot, WaitingFor};
getNextState({UniqueId, {LastBallot, LastValue}, _, WaitingFor}, {nextballot, Ballot, ReturnPid}) ->
  ReturnPid ! {lastvote, UniqueId, LastBallot, LastValue, Ballot},
  {UniqueId, {LastBallot, LastValue}, Ballot, WaitingFor};
 
getNextState({UniqueId, LastVote, {Number, Id}, WaitingFor}, {beginballot, {NewNumber, _}, _, ReturnPid}) when Number > NewNumber ->
  ReturnPid ! ignored,
  {UniqueId, LastVote, {Number, Id}, WaitingFor};
getNextState({UniqueId, _, _, WaitingFor}, {beginballot, Ballot, Value, ReturnPid}) ->
  ReturnPid ! {voted, UniqueId, Ballot},
  {UniqueId, {Ballot, Value}, Ballot, WaitingFor};

getNextState({UniqueId, PrevVote, CurrentBallot, WaitingFor}, {voted, Id, Ballot}) ->
  Votes = get(votes), Flag = lists:member(Id, WaitingFor), 
  %%?debugFmt("****************** ~n Old Votes: ~w New Vote: ~w ~n ****************** ~n", [Votes, Ballot]),
  if
	Flag -> UpdatedVotes = lists:append(Votes,[Ballot]), 
		%%?debugFmt("****************** ~n Votes: ~w ~n ****************** ~n", [UpdatedVotes]),
		put(votes, UpdatedVotes), 
		RemainingVotes = lists:delete(Id, WaitingFor), 
		{UniqueId, PrevVote, CurrentBallot, RemainingVotes};
        true -> {UniqueId, PrevVote, CurrentBallot, WaitingFor}
  end;
 
getNextState({_, _, _, _}, {success, Value, _}) ->
  success(Value);
 
getNextState({UniqueId, {LastBallot, LastValue}, CurrentBallot, _}, {proposevalue, Value}) ->
  SynodIds = get(synod_ids),
  lists:foreach(fun(Id) ->
        Pid = whereis(Id),
        Pid ! {nextballot, CurrentBallot, self()}
    end, SynodIds),
  put(proposal_state, next),
  put(quorum_timer, now()),
  {UniqueId, {null, Value}, CurrentBallot, []};

getNextState({UniqueId, {LastBallot, LastValue}, CurrentBallot, _}, {proposevalue, Key, Value}) ->
  SynodIds = get(synod_ids),
  put(Key, Value),
  lists:foreach(fun(Id) ->
        Pid = whereis(Id),
        Pid ! {nextballot, CurrentBallot, self()}
    end, SynodIds),
  put(proposal_state, next),
  put(quorum_timer, now()),
  {UniqueId, {null, Value}, CurrentBallot, []};
 
getNextState({UniqueId, {LastBallot, LastValue}, CurrentBallot, WaitingFor}, {lastvote, Id, Ballot, Value, _}) when ((Ballot > LastBallot) and (Ballot /= null)) ->
  UpdatedVoters = lists:append([Id], WaitingFor),
  {UniqueId, {Ballot, Value}, CurrentBallot, UpdatedVoters};
getNextState({UniqueId, {LastBallot, LastValue}, CurrentBallot, WaitingFor}, {lastvote, Id, Ballot, _, _})  ->
  UpdatedVoters = lists:append([Id], WaitingFor),
  {UniqueId, {LastBallot, LastValue}, CurrentBallot, UpdatedVoters};

 
getNextState({UniqueId, LastVote, CurrentBallot, WaitingFor}, {status, ReturnPid}) ->
  Timer = get(quorum_timer),
  Diff = timer:now_diff(now(),Timer),
  {_, Value} = LastVote,
  %%?debugFmt("****************** ~n Vote Value: ~w ~n ****************** ~n", [LastVote]),
  Members = get(synod_ids),
  Size = length(Members),
  Majority = Size/2,
  QuorumSize = length(WaitingFor),
  %%?debugFmt("****************** ~n Time: ~w Value: ~w ~n ****************** ~n", [Diff, QuorumSize]),
  Proposal = get(proposal_state),
  if
	  (Proposal == next) ->
		  if
			(( Diff >= 11500) and (QuorumSize < Majority)) -> ReturnPid ! aborted;
			(( Diff >= 11500) and (QuorumSize >= Majority)) -> ReturnPid ! {voted, QuorumSize - 1}, put(proposal_state, beginState), put(votes, []);
			(QuorumSize == Size) -> ReturnPid ! {voted, QuorumSize - 1}, put(proposal_state, beginState), put(votes, []);
			true -> ReturnPid ! {nextballot, Value, Size - QuorumSize}
		  end;
	  (Proposal == beginState) -> 
		if 
			(( Diff >= 11500) and (QuorumSize - 1 > 0)) -> ReturnPid ! aborted;
			(QuorumSize - 1 =< 0) -> ReturnPid ! {success, Value};
			true -> ReturnPid ! {voted, QuorumSize - 1}
		end	
  end,
  {UniqueId, LastVote, CurrentBallot, WaitingFor};

getNextState({UniqueId, LastVote, CurrentBallot, WaitingFor}, startVote) ->
  put(proposal_state, beginState),
  put(votes, []),
  {Ballot, Value} = LastVote,
  lists:foreach(fun(Id) ->
        Pid = whereis(Id),
        Pid ! {beginballot, CurrentBallot, Value, self()}
    end, WaitingFor),
  {UniqueId, LastVote, CurrentBallot, WaitingFor};

getNextState({UniqueId, LastVote, CurrentBallot, WaitingFor}, {status, Key, ReturnPid}) ->
  Timer = get(quorum_timer),
  Diff = timer:now_diff(now(),Timer),
  KeyValue = get(Key),
  {_, Value} = LastVote,
  Members = get(synod_ids),
  Size = length(Members),
  Majority = Size/2,
  QuorumSize = length(WaitingFor),
  %% ?debugFmt("****************** ~n Time: ~w Value: ~w ~n ****************** ~n", [Diff, QuorumSize]),
  Proposal = get(proposal_state),
  if
	  (Proposal == next) ->
		  if
			(( Diff >= 11100) and (QuorumSize < Majority)) -> ReturnPid ! aborted;
			(( Diff >= 11100) and (QuorumSize >= Majority)) -> put(proposal_state, beginState), put(votes, []), ReturnPid ! {voted, QuorumSize - 1};
			(QuorumSize == Size) -> put(proposal_state, beginState), put(votes, []), ReturnPid ! {voted, QuorumSize - 1} ;
			true -> ReturnPid ! {nextballot, KeyValue, Size - QuorumSize + 1}
		  end;
	  (Proposal == beginState) -> 
		if 
			(( Diff >= 11100) and (QuorumSize - 1 /= 0)) -> ReturnPid ! aborted;
			(QuorumSize - 1 == 0) -> ReturnPid ! {success, KeyValue};
			true -> ReturnPid ! {voted, QuorumSize - 1}
		end	
  end,
  {UniqueId, LastVote, CurrentBallot, WaitingFor}.
 
subtract(List1,List2) ->
    lists:filter(fun(X) -> not(lists:member(X,List2)) end, List1).

success(Value) ->
  receive
    {nextballot, _, ReturnPid} ->
      ReturnPid ! {success, Value},
      success(Value)
  end.
 
start_synod_member(UniqueId) ->
  Pid = spawn(fun() -> heartbeat({UniqueId}) end),
  register(UniqueId, Pid).
 
% THE TESTME Function sets up a test with a running synod member
% that is then killed after the test runs
 
setup() ->
  start_synod_member(synod1),
  start_synod_member(disabled1),
  start_synod_member(disabled2),
  start_synod_member(disabled3),
  start_synod_member(disabled4),
  disable_member(disabled1),
  disable_member(disabled2),
  disable_member(disabled3),
  disable_member(disabled4).
 
 
cleanup(_) ->
    exit(whereis(synod1),kill),
    exit(whereis(disabled1),kill),
    exit(whereis(disabled2),kill),
    exit(whereis(disabled3),kill),
    exit(whereis(disabled4),kill),
    timer:sleep(10). % give it a little time to die
 
testme(Test) ->
    {setup, fun setup/0, fun cleanup/1, [ Test ] }.
 
 
 
% TEST 
% to run ALL tests, use paxos:test()
% You can uncomment the various tests as you go.
start_synod_memeber_test_() ->
    testme(?_test(
              ?assert(whereis(synod1) =/= undefined)
             )).
 
 
% This causes the synod member to create a ballot number that has not
% been used thus far.  It should be of the form {BallotNumber,
% UniqueId}, UniqueId is the id of the member.  BallotNumber should be
% 1+the largest ballot the synod member has currently seen.  This
% should not change the state of the synod member.  If the synod
% member does not reply in a reasonable interval (say 50 ms), your
% function should return ignored.
 
generate_unused_ballot_number(UniqueId) ->
  send_with_timeout(UniqueId, {genballot}).
 
unused_ballot_test_() ->
    testme(?_test(
              ?assertEqual({1,synod1},generate_unused_ballot_number(synod1))
             )).
 
 
 
% This puts the synod member in a state where it no longer responds to
% messages.  Any messages sent should be lost (i.e. not ever
% recieved), except (of course) for enable_synod_member.
disable_member(UniqueId) ->
  Pid = whereis(UniqueId),
  Pid ! disable.
 
 
% This puts the synod member back in normal state
enable_member(UniqueId) ->
  Pid = whereis(UniqueId),
  Pid ! enable.
 
enable_disable_ballot_test_() ->
    testme(?_test([
                   ?assertEqual({1,synod1},generate_unused_ballot_number(synod1)),
                   disable_member(synod1),
                   ?assertEqual(ignored,generate_unused_ballot_number(synod1)),
                   ?assertEqual(ignored,generate_unused_ballot_number(synod1)),
                   enable_member(synod1),
                   ?assertEqual({1,synod1},generate_unused_ballot_number(synod1))
             ])).
 
 
 
% This sends a nextballot request to the Synod member.  The function
% should return a response of the form {lastvote, UniqueId, B,V,Bnew}
% if the member has participated in a previous ballot B with value V.
% Bnew is the new ballot sent by the request.  If the member has
% participated in no previous ballot, it should return
% {lastvote,UniqueId, null, null, Bnew}.  If the member is
% participating in a greater ballot, the function should return
% "ignored".  Also, if the member does not return (times out), it
% should return "ignored".
%
% Note that although it may be tempting, your synod members should
% not use this function when contacting others.  It blocks on response
% which is very inefficient.
send_nextballot(UniqueId,Bnew) ->
  send_with_timeout(UniqueId, {nextballot, Bnew}).
 
nextballot1_test_() ->
    testme(?_test([
                   ?assertEqual({lastvote,synod1,null,null,{1,fake}},
                                send_nextballot(synod1,{1,fake})),
                   % should participate in larger ballots
                   ?assertEqual({lastvote,synod1,null,null,{3,fake}},
                                send_nextballot(synod1,{3,fake})),
                   % should ignore lower ballots
                   ?assertEqual(ignored,
                                send_nextballot(synod1,{2,fake})),
                   % should ignore lower ballots
                   ?assertEqual(ignored,
                                send_nextballot(synod1,{1,fake}))])).
 
 
 
 
% This sends a beginballot request to the Synod member.  If the member
% has not participated in any larger ballot since the lastvote
% response, the function should return {voted,UniqueId, B}.  If the
% member has participated in a new ballot (or the member is
% unresponsive) the function should return ignored.
%
% Note that although it may be tempting, your synod members should
% not use this function when contacting others.  It blocks on response
% which is very inefficient.
send_beginballot(UniqueId,B,Value) ->
  send_with_timeout(UniqueId, {beginballot, B, Value}).
 

beginballot1_test_() ->
    testme(?_test([
                   ?assertEqual({lastvote,synod1,null,null,{1,fake}},
                                send_nextballot(synod1,{1,fake})),
                   % now a vote
                   ?assertEqual({voted,synod1,{1,fake}},
                                send_beginballot(synod1,{1,fake},coolvalue)),
                   % subsequent nextballots should get new value
                   ?assertEqual({lastvote,synod1, {1,fake},coolvalue,{2,fake}},
                                send_nextballot(synod1,{2,fake})),
                   % but if a new ballot is in progress...
                   ?assertEqual({lastvote,synod1, {1,fake},coolvalue,{3,fake}},
                                send_nextballot(synod1,{3,fake})),
                   % earlier ballots are ignored...
                   ?assertEqual(ignored,
                                send_beginballot(synod1,{2,fake},othervalue)),
                   % and don't update values
                   ?assertEqual({lastvote,synod1,{1,fake},coolvalue,{4,fake}},
                                send_nextballot(synod1,{4,fake})),
                   % but newer ballots do update the value
                   ?assertEqual({voted,synod1,{4,fake}},
                                send_beginballot(synod1,{4,fake},updatedvalue)),
                   ?assertEqual({lastvote,synod1,{4,fake},updatedvalue,{5,fake}},
                                send_nextballot(synod1,{5,fake}))
 
                  ])). 
 
 
% This sends a success request to the synod member.  The member should
% not return anything, but the member's state should be updated so
% that the value in considered resolved.  Subsequent nextballot
% requests should return {success,Value} and it should not be possible
% to change the systems state from this point.  The send_success
% function itself should return ok.
 
send_success(UniqueId,Value) ->
  Pid = whereis(UniqueId),
  Pid ! {success, Value, self()},
  ok.
 
success1_test_() ->
    testme(?_test([
                   ?assertEqual({lastvote,synod1,null,null,{1,fake}},
                                send_nextballot(synod1,{1,fake})),
                   % now a vote
                   ?assertEqual({voted,synod1,{1,fake}},
                                send_beginballot(synod1,{1,fake},coolvalue)),
                   % vote went through!  success
                   ?assertEqual(ok,
                                send_success(synod1,coolvalue)),
                   % now state is stuck
                   ?assertEqual({success,coolvalue},
                                send_nextballot(synod1,{2,fake}))
                  ])).
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PART 2: Synod Ballot Running (25 Points)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
%%%% Ok at this point your synod members should be doing the right
%%%% thing assuming you pass the tests.  Now we need them to start and
%%%% run ballots.  
 
% Sets the list of all memebers in the Synod.  This returns ok or
% ignored if the synod member is offline.
set_members(UniqueId,ListOfAllSynodUniqueIds) ->
  send_with_timeout(UniqueId, {setmembers, ListOfAllSynodUniqueIds}).
 
set_members_test_() ->
    testme(?_test([
                   ?assertEqual(ok, set_members(synod1,[one,two,three])),
                   disable_member(synod1),
                   ?assertEqual(ignored, set_members(synod1,[one,two,three])),
                   enable_member(synod1),
                   ?assertEqual(ok, set_members(synod1,[one,two,three]))
                  ])).
 
 
% starts the process of proposing a value to the synod, using the
% given BallotNumber.  It should send next ballot to all members - it
% should not wait for responses but just return ok.
%
% If another start_propose_value occurs when another is in process, it
% MAY abort the current process and make a new process.
start_propose_value(UniqueId, PossibleValue) ->
  Pid = whereis(UniqueId),
  Pid ! {proposevalue, PossibleValue},
  ok.
 
% lets a test act like a synod member by sending responses that look
% like they come from a specific sender.  The real senders will be
% disabled, so the tests can ensure only fake responses will be
% considered
%
% NOTE: in lastvote, it is possible that some (but not all) members
% may respond.  The system should wait 100 milliseconds even after
% reaching qurom to see if any additional responses arrive (it's
% better if everyone participates if possible).  If a quorom is not
% reached in 100 milliseconds you should abort the process entirely.
send_fake_lastvote(ReceiverUniqueId,FakeSenderUniqueId,PrevBallot,PrevVote,NewBallot) ->
  Pid = whereis(ReceiverUniqueId),
  Pid ! {lastvote, FakeSenderUniqueId, PrevBallot, PrevVote, NewBallot}.
 
 
% Returns the state of the proposal in process.  What it returns
% depends on the state:
%
% {nextballot,CurrentValue,NumberOfMembersNotResponded}: nextballots
% sent but still waiting for responses.
%
% {voted,NumberOfQuorumNotResponded}: beginballots
% sent but still waiting for responses.
%
% {success,FinalValue}: final value set 
%
% aborted: the process was aborted because qurom was not reached
% within the alloted timeframe.
get_proposal_state(UniqueId) ->
  send_with_timeout(UniqueId, {status}).
 
% first, let's just test we can correctly get into the nextballot
% state and return responses note that synod1 is also in the
% responders
propose_nextballot1_test_() ->
    testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                   ?assertEqual(ok, start_propose_value(synod1,value)),
                   timer:sleep(10),
                   ?assertEqual({nextballot,value,2}, 
                                get_proposal_state(synod1)),
                   send_fake_lastvote(synod1,disabled3,null,null,{1,synod1}),
                   ?assertEqual({nextballot,value,1}, 
                                get_proposal_state(synod1))
                  ])).
 
 
% Ok, now let's simulate some previous failed ballots to ensure the
% right value wins
propose_nextballot2_test_() ->
    testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled1,disabled2,disabled3,disabled4])),
                   % first some lastvote messages to increase the ballot num
                   ?assertEqual({lastvote,synod1,null,null,{1,disabled1}},
                                send_nextballot(synod1,{1,disabled1})),
                   ?assertEqual({lastvote,synod1,null,null,{2,disabled2}},
                                send_nextballot(synod1,{2,disabled2})),
                   ?assertEqual({lastvote,synod1,null,null,{3,disabled3}},
                                send_nextballot(synod1,{3,disabled3})),
                   ?assertEqual(ok, start_propose_value(synod1,value)),
                   timer:sleep(10),
                   % initially proposed value is used
                   ?assertEqual({nextballot,value,4}, 
                                get_proposal_state(synod1)),
                   send_fake_lastvote(synod1,disabled1,{1,disabled1},val1,{4,synod1}),
                   % but then an oldvalue replaces the proposed
                   ?assertEqual({nextballot,val1,3}, 
                                get_proposal_state(synod1)),
                   % then another, later vote replaces that
                   send_fake_lastvote(synod1,disabled3,{3,disabled3},val3,{4,synod1}),
                   ?assertEqual({nextballot,val3,2}, 
                                get_proposal_state(synod1)),
                   % then an earlier vote comes up, its value is ignored
                   send_fake_lastvote(synod1,disabled2,{2,disabled2},val2,{4,synod1}),
                   ?assertEqual({nextballot,val3,1}, 
                                get_proposal_state(synod1))
 
 
                  ])).
 
% Ok, now assure that if a beginballot has happened, a node returns the next value
 propose_nextballot3_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled1,disabled2,disabled3])),
                    enable_member(disabled1),
                    % first some lastvote messages to increase the ballot num
                    ?assertEqual({lastvote,disabled1,null,null,{1,disabled2}},
                                 send_nextballot(disabled1,{1,disabled2})),
                    ?assertEqual({lastvote,synod1,null,null,{1,disabled2}},
                                 send_nextballot(synod1,{1,disabled2})),
                    % only disabled1 (not disabled in this test case) gets
                    % the beginballot message
                    ?assertEqual({voted,disabled1,{1,disabled2}},
                                 send_beginballot(disabled1,{1,disabled2},coolvalue)),
                    % now synod1 tries to propose
                    ?assertEqual(ok, start_propose_value(synod1,value)),
                    timer:sleep(10),
                    % disabled1 should ensure value is correctly returned
                    ?assertEqual({nextballot,coolvalue,2}, 
                                 get_proposal_state(synod1))
                   ])).
 
% ensure we report aborted if we don't get enough participation
 propose_nextballot4_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    ?assertEqual(ok, start_propose_value(synod1,value)),
                    timer:sleep(10),
                    ?assertEqual({nextballot,value,2}, 
                                 get_proposal_state(synod1)),
                    timer:sleep(100),
                    ?assertEqual(aborted,
                                 get_proposal_state(synod1)),
                    % assure that aborts are not forever
                    % we can start a new proposal if we need to
                    ?assertEqual(ok, start_propose_value(synod1,value)),
                    timer:sleep(10),
                    ?assertEqual({nextballot,value,2}, 
                                 get_proposal_state(synod1))
 
                   ])).
 
 
 
% Woo!  On to the next stage!  We would like to be able to send a fake
% voted response.
%
% NOTE: in voted, we require that all those who participated in
% lastvote now respond (not just > 50% or whatever).  Of course, not
% everybody might have responded to lastvote, so that might not be
% every member.  But every member who is in the qurom must now reply
% with voted.  The system should wait 100 milliseconds .  If 100%
% qurom participation doesn't happen, the system should abort.  Note
% that as usual, aborting doesn't mean the data is lost (the quorm
% members will ensure it gets propigated at lastvote).
send_fake_voted(ReceiverUniqueId,FakeSenderUniqueId,NewBallot) ->
    Pid = whereis(ReceiverUniqueId),
    Pid ! {voted, FakeSenderUniqueId, NewBallot}.
 
 
% now we can just about get to the end of the process
 propose_voted1_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    ?assertEqual(ok, start_propose_value(synod1,value)),
                    send_fake_lastvote(synod1,disabled3,null,null,{1,synod1}),
                    send_fake_lastvote(synod1,disabled2,null,null,{1,synod1}),
                    timer:sleep(10), % a little sleep to ensure everyting processes
                    ?assertEqual({voted,2}, 
                                 get_proposal_state(synod1)),
                    send_fake_voted(synod1,disabled3,{1,synod1}),
                    ?assertEqual({voted,1}, 
                                 get_proposal_state(synod1)),
                    % hey a duplicate message!  shouldn't change the state
                    send_fake_voted(synod1,disabled3,{1,synod1}),
                    ?assertEqual({voted,1}, 
                                 get_proposal_state(synod1)),
                    % finally we've got disabled 2 responding
                    send_fake_voted(synod1,disabled2,{1,synod1}),
                    timer:sleep(10), % a little sleep to ensure everyting processes
                    ?assertEqual({success,value},
                                 get_proposal_state(synod1))
                   ])).
 
% this one tests that we proceed even when we having a missing lastvote
% we will proceed if more than 50% of members responed
 propose_voted2_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    ?assertEqual(ok, start_propose_value(synod1,value)),
                    send_fake_lastvote(synod1,disabled3,null,null,{1,synod1}),
                    % disabled2 never responds
                    timer:sleep(110), % wait a long time to ensure a timeout
                    ?assertEqual({voted,1}, 
                                 get_proposal_state(synod1)),
                    send_fake_voted(synod1,disabled3,{1,synod1}),
                    timer:sleep(10), % a little sleep to ensure everyting processes
                    ?assertEqual({success,value},
                                 get_proposal_state(synod1))
                   ])).
 
 
% now we test aborted
 propose_voted3_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    ?assertEqual(ok, start_propose_value(synod1,value)),
                    send_fake_lastvote(synod1,disabled3,null,null,{1,synod1}),
                    send_fake_lastvote(synod1,disabled2,null,null,{1,synod1}),
                    timer:sleep(10), % a little sleep to ensure everyting processes
                    ?assertEqual({voted,2}, 
                                 get_proposal_state(synod1)),
                    send_fake_voted(synod1,disabled3,{1,synod1}),
                    ?assertEqual({voted,1}, 
                                 get_proposal_state(synod1)),
                    % disabled 2 never responds
                    timer:sleep(110), 
                    ?assertEqual(aborted,
                                 get_proposal_state(synod1))
                   ])).
 
 
% The final stage of Part 1.  Proposes a particular value.  Returns:
% {success,Value} if the storage was successful.  Value could be proposed
% value, or some other (previously proposed) that the synod algorithm
% settled on.  Otherwise returns ignored.  In that case the value
% might or might not be successfully stored.
 
propose_value(UniqueId, PossibleValue) ->
  Pid = whereis(UniqueId),
  Pid ! {proposevalue, PossibleValue},
  timer:sleep(50),
  Status = get_proposal_state(UniqueId),
  ?debugFmt("****************** ~n Status: ~w ~n ****************** ~n", [Status]),
  if
	(size(Status) == 2) ->    Pid ! startVote,
  				  timer:sleep(50),
				  Result = get_proposal_state(UniqueId),
				  if
					(Result == aborted) -> ignored;
					true -> Result
				  end;
        true -> ignored
  end.
 
% a test with 3 working synod members
 propose1_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    enable_member(disabled2),
                    enable_member(disabled3),
                    ?assertEqual({success,value}, propose_value(synod1,value))
                   ])).
 
% a test with 2 working synod members, out of 3
 propose2_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    enable_member(disabled2),
                    %disabled3 is still disabled
                    ?assertEqual({success,value}, propose_value(synod1,value))
                   ])).
 
% a test with one synod member - can't set a value
 propose3_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    %disabled2 is still disabled
                    %disabled3 is still disabled
                    ?assertEqual(ignored, propose_value(synod1,value))
                   ])).
 
% where a ballot initially fails, but then the old value is used again
 propose4_test_() ->
     testme(?_test([?assertEqual(ok, set_members(synod1,[synod1,disabled2,disabled3])),
                    ?assertEqual(ok, start_propose_value(synod1,value)),
                    timer:sleep(10),
                    send_fake_lastvote(synod1,disabled3,null,null,{1,synod1}),
                    ?assertEqual({nextballot,value,1}, 
                                 get_proposal_state(synod1)),
                    timer:sleep(250),
                    ?assertEqual(aborted,
                                 get_proposal_state(synod1)),
                    % assure that aborts are not forever
                    % we can start a new proposal if we need to
                    enable_member(disabled2),
                    enable_member(disabled3),
                    ?assertEqual({success,value}, propose_value(synod1,newValue))
 
                   ])).
 
 
 
 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PART 3: Multiple Values (25 Points)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
% Now we want to expand the synod algorithm to handle multiple values
% at once.  In the complete paxos algorithm, this is accompished by
% storing an indexed list -- that involves a lot of bookkeeping but is
% better because the increasing index makes it easy to bring new
% members up to speed, figure out if data is missing etc.
%
% We're going to be lazier.  We are going to make a key value store,
% with each key individually decided by a synod algorithm.  This means
% that once a particular key/value is set, it can't be changed.
%
% As before, exactly how you structure it is up to you...but reuse
% that synod code above unless you really are a glutton for
% punishment.
 
start_paxos_member(UniqueId) ->
    Pid = spawn(fun() -> heartbeat({UniqueId}) end),
    register(UniqueId, Pid).
 
setup2() ->
    start_paxos_member(paxos1),
    start_paxos_member(pdisabled1),
    start_paxos_member(pdisabled2),
    disable_member(pdisabled1),
    disable_member(pdisabled2).
 
cleanup2(_) ->
    exit(whereis(paxos1),kill),
    exit(whereis(pdisabled1),kill),
    exit(whereis(pdisabled2),kill),
    timer:sleep(10). % give it a little time to die
 
testme2(Test) ->
    {setup, fun setup2/0, fun cleanup2/1, [ Test ] }.
 
 
 set_members2_test_() ->
     testme2(?_test([
                    ?assertEqual(ok, set_members(paxos1,[one,two,three])),
                    disable_member(paxos1),
                    ?assertEqual(ignored, set_members(paxos1,[one,two,three])),
                    enable_member(paxos1),
                    ?assertEqual(ok, set_members(paxos1,[one,two,three]))
                   ])).
 
 
 
 
% disable disable_member, enable_member, and set_members should work
% identically to synod members
 
% as above but with the key of the proposal we care about
get_proposal_state(UniqueId,Key) ->
        send_with_timeout(UniqueId, {status, Key}).
 
 
% As start proposed_value above, but with a key.  This doubles as both
% a "get" and "set" because it will return the old value if things are
% already set.  We ought to build a seperate "getter" that did a
% lastballot but didn't proceed to voting if everybody voted null.
% But this is not a real system, so we'll just be lazy.
%
% Note that several proposals need to be executable at the same time.
start_propose_value(UniqueId,Key,PossibleValue) ->
  Pid = whereis(UniqueId),
  Pid ! {proposevalue, Key, PossibleValue},
  ok.
 
 
 
 propose_paxos1_test_() ->
     testme2(?_test([?assertEqual(ok, set_members(paxos1,[paxos1,pdisabled1,pdisabled2])),
                    ?assertEqual(ok, start_propose_value(paxos1,key1,value)),
                    ?assertEqual(ok, start_propose_value(paxos1,key2,value2)),
                    timer:sleep(10),
                    ?assertEqual({nextballot,value,2}, 
                                 get_proposal_state(paxos1,key1)),
                    ?assertEqual({nextballot,value2,2}, 
                                 get_proposal_state(paxos1,key2))
                   ])).
 
 
% as propose_value above, but with a Key
propose_value(UniqueId,Key,ProposedValue) ->
    solveme.
 
 
%% propose_paxos2_test_() ->
%%     testme2(?_test([?assertEqual(ok, set_members(paxos1,[paxos1,pdisabled1,pdisabled2])),
%%                    enable_member(pdisabled1),
%%                    enable_member(pdisabled2),
%%                    ?assertEqual({success,value}, propose_value(paxos1,key,value)),
%%                    ?assertEqual({success,valueBar}, propose_value(paxos1,keyFoo,valueBar)),
%%                    ?assertEqual({success,val3}, propose_value(paxos1,key3,val3))
%%                   ])).
 
%% propose_paxos3_test_() ->
%%     testme2(?_test([?assertEqual(ok, set_members(paxos1,[paxos1,pdisabled1,pdisabled2])),
%%                    enable_member(pdisabled1),
%%                    % leaving 2 disabled so the process must go paralell
%%                    ?assertEqual(ok, start_propose_value(paxos1,key,value)),
%%                    ?assertEqual({success,valueBar}, propose_value(paxos1,keyFoo,valueBar)),
%%                    ?assertEqual(ok, start_propose_value(paxos1,key2,value2)),
%%                    ?assertEqual({success,value}, propose_value(paxos1,key,otherValue)),
%%                    ?assertEqual({success,val3}, propose_value(paxos1,key3,val3))
%%                   ])).
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PART 3: Monitoring (25 points)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
% We want to have a monitoring process that ensures all the paxos
% instances stay alive.  Make a new process for starting and stopping
% paxos members.  If a paxos member dies (maybe because some jerk sent
% an end_paxos_member command) the monitor should restart it.
 
% This startup should work on remote systems, which means you'll have
% to stop using register and whereis.  Instead, you should use
% global:register_name and global:whereis_name.  BUT you don't have to
% modify all your code - go ahead just make the function work that way.
 
monitor_loop() -> process_flag(trap_exit, true),
	receive
		{new, UniqueId, Server} ->
			Pid = spawn_link(Server, fun() -> heartbeat({UniqueId}, Server) end),
			io:format("Registered process ~w with Pid ~w on ~w ~n",[UniqueId, Pid, Server]),
			global:register_name(UniqueId, Pid),
			monitor_loop();
		{'EXIT', From, Reason} -> {Id, Server} = Reason,
			io:format("The process ~w died on Server ~w ~n --restarting-- ~n",[Id, Server]),
			self() ! {new, Id, Server},
			monitor_loop();
		bye -> goodbye
	end.

% causes the paxos member to quit
end_paxos_member(UniqueId) ->
    Pid = global:whereis_name(UniqueId),
    Pid ! exit,
    ok.
 
 
% Creates a monitor and returns its process id
start_paxos_monitor() ->
    spawn(fun() -> monitor_loop() end).
 
% create a new paxos member and start monitoring it
% it should print a message if it restarts an instance
%
% Note:it should restart the instances on the same server
% they were originally started on
create_monitored_member(MonitorProcessId, UniqueId, ServerToStartOn) ->
    MonitorProcessId ! {new, UniqueId, ServerToStartOn},
    ok.
 
% No unit tests for this one, but here's an example in operation.
 
%% (buffalo@68.217.120.210)1> erlang:set_cookie(node(),'BLAHBLAHBLAH').
%% true
%% (buffalo@68.217.120.210)2> net_adm:ping('buffalo@erlang.csse.rose-hulman.edu').
%% pong
%% (buffalo@68.217.120.210)3> nl(paxos).
%% abcast
%% (buffalo@68.217.120.210)4> Mom = paxos:start_paxos_monitor().
%% <0.50.0>                    
%% (buffalo@68.217.120.210)5>  paxos:create_monitored_member(Mom,paxos1,'buffalo@erlang.csse.rose-hulman.edu'). 
%% ok
%% PID <7250.77.0> Unique id paxos1 started
%% (buffalo@68.217.120.210)6>  paxos:create_monitored_member(Mom,paxos2,'buffalo@erlang.csse.rose-hulman.edu').
%% ok
%% PID <7250.78.0> Unique id paxos2 started
%% (buffalo@68.217.120.210)7>  paxos:create_monitored_member(Mom,paxos3,node()).
%% ok                          
%% PID <0.54.0> Unique id paxos3 started
%% (buffalo@68.217.120.210)8> paxos:end_paxos_member(paxos2).
%% true
%% PID <7250.78.0> Unique id paxos2 died -- restarting -- new Pid <7250.79.0>
%% (buffalo@68.217.120.210)9> 
