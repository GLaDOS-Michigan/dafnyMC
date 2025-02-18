// Chapter 5 Exercise 1, 2
//#title Two Phase Commit Model
//#desc Model a distributed protocol using compound state machines.

/*
 * Your goal is to model a 2-Phase Commit protocol. You're modeling a single
 * instance of the problem -- a designated coordinator, no concurrent
 * instances. Furthermore, you may assume there are no coordinator or
 * participant failures. This is indeed a fairly simplistic setting, but it's
 * still nontrivial, and is a nice example for reasoning about the
 * state-machine composition framework.
 *
 * 2-Phase Commit Protocol english design doc:
 *
 * 1, Coordinator sends VOTE-REQ to all participants.
 * 2. Each participant i sends back vote_i to coordinator.
 *     If vote_i=No then i sets decision_i := Abort.
 * 3. Coordinator collects votes.
 *     If all votes are yes then coordinator sets decision_c := Commit and sends
 *     Commit to all participants.
 *     Else coordinator sets decision_c := Abort and sends Abort to all
 *     participants who voted yes.
 * 4. Participants receiving Commit set decision_i := Commit
 *     (The slide is delightfully poorly specified. "else decision_i := Abort"!?
 *     When else? As soon as it doesn't hear Commit!?)
 *
 * This file provides a lot of helpful framework. You only need to
 * define Types.Message and then fill in the state machine types and actions
 * in module CoordinatorHost and module ParticipantHost.
 *
 * Unlike chapter01, where you could work exercises sequentially,
 * WE STRONGLY ENCOURAGE YOU to read the entire file before beginning
 * work. Later pieces of the file are helpful, for example by explaining
 * the network model you're working in, and by helping you understand
 * the role the Constants datatypes play.
 */

include "library.dfy" // Some handy utilities.
module CommitTypes {
    // How a particular participant feels.
    datatype Vote = Yes | No
    // What decision has been reached by the protocol.
    datatype Decision = Commit | Abort
}


module Types {
    import opened Library
    import opened CommitTypes

    type HostId = nat

    // Have to define our message datatype so network can refer to it.
    // (There are cleverer ways to parameterize the network module, but
    // we're trying to avoid getting fancy with the Dafny module system.)
    datatype Message =
        | VoteReqMsg                                                     // from leader
        | VoteMsg(sender: HostId, vote: Vote)    // from participant
        | DecisionMsg(decision: Decision)

    // Should have been a parameterized type in library.dfy
    datatype Msg_Option = Some(value:Message) | None

    // A MessageOps is a "binding variable" used to connect a Host's Next step
    // (what message got received, what got sent?) with the Network (only allow
    // receipt of messages sent prior; record newly-sent messages).
    // Note that both fields are Option. A step predicate can say recv.None?
    // to indicate that it doesn't need to receive a message to occur.
    // It can say send.None? to indicate that it doesn't want to transmit a message.
    datatype MessageOps = MessageOps(recv:Msg_Option, send:Msg_Option)
}

// There are two host roles in 2PC, Coordinator and Participant. We'll define
// separate state machines for each.
// This state machine defines how a coordinator host should behave: what state
// it records, and what actions it's allowed to take in response to incoming
// messages (or spontaneously by thinking about its existing state).
module CoordinatorHost {
    import opened CommitTypes
    import opened Types
    import opened Library

    datatype Constants = Constants(participantCount: nat)

    // What relationship must hold between this host's own constants and the
    // structure of the overall group of hosts? It needs to have a correct
    // count of the number of participants.
    predicate ConstantsValidForGroup(c: Constants, participantCount: nat)
    {
        && c.participantCount == participantCount
    }

    // Should have been a parameterized type in library.dfy
    datatype Vote_Option = Some(value:Vote) | None
    datatype Decision_Option = Some(value:Decision) | None

    datatype Variables = Variables(votes: seq<Vote_Option>, decision: Decision_Option)

    // WF is for a simple condition that relates every valid Variables state
    // to the Constants.
    predicate WF(c: Constants, v:Variables) {
        && |v.votes| == c.participantCount
    }

    predicate Init(c: Constants, v: Variables)
    {
        && WF(c, v)
        // No votes recorded yet
        && (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].None?)
        // No decision recorded yet
        && v.decision.None?
    }

    // Protocol steps. Define an action predicate for each step of the protocol
    // that the coordinator is involved in.
    // Hint: it's probably easiest to separate the receipt and recording of
    // incoming votes from detecting that all have arrived and making a decision.
    predicate SendReq(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && WF(c, v)
        && WF(c, v')
        && msgOps == MessageOps(Msg_Option.None, Msg_Option.Some(VoteReqMsg))
        && v' == v    // UNCHANGED everything.
    }

    predicate LearnVote(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && WF(c, v)
        && WF(c, v')
        && msgOps.recv.Some?
        && var recvMsg := msgOps.recv.value;
        && recvMsg.VoteMsg?
        && recvMsg.sender < c.participantCount
        // Record sender's vote.
        && v' == v.(votes := v.votes[recvMsg.sender := Vote_Option.Some(recvMsg.vote)])
        && msgOps.send.None?
    }

    predicate AllVotesCollected(c: Constants, v: Variables)
    {
        && WF(c, v)
        && (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].Some?)
    }

    predicate ObservesResult(c: Constants, v: Variables, decision: Decision)
    {
        && WF(c, v)
        && AllVotesCollected(c, v)
        && decision ==
            if (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].value.Yes?)
            then Commit
            else Abort
    }

    predicate Decide(c: Constants, v: Variables, v': Variables, decision: Decision, msgOps: MessageOps)
    {
        && WF(c, v)
        && WF(c, v')
        && msgOps.recv.None?
        && ObservesResult(c, v, decision)
        // Record the decision
        && v' == v.(decision := Decision_Option.Some(decision))
        // Transmit the decision
        && msgOps.send == Msg_Option.Some(DecisionMsg(decision))
    }

    // JayNF
    datatype Step =
        | SendReqStep
        | LearnVoteStep
        | DecideStep(decision: Decision)

    // msgOps is a "binding variable" -- the host and the network have to agree
    // on its assignment to make a valid transition. So the host explains what
    // would happen if it could receive a particular message, and the network
    // decides whether such a message is available for receipt.
    predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
    {
        match step
            case SendReqStep => SendReq(c, v, v', msgOps)
            case LearnVoteStep => LearnVote(c, v, v', msgOps)
            case DecideStep(decision) => Decide(c, v, v', decision, msgOps)
    }

    predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists step :: NextStep(c, v, v', step, msgOps)
    }
}

module ParticipantHost {
    import opened CommitTypes
    import opened Types
    import opened Library
    import opened CoordinatorHost

    datatype Constants = Constants(hostId: HostId, preference: Vote)

    // What relationship must hold between this host's own constants and the
    // structure of the overall group of hosts? It needs to know its hostId.
    predicate ConstantsValidForGroup(c: Constants, hostId: HostId)
    {
        && c.hostId == hostId
    }

    datatype Variables = Variables(decision: Decision_Option)

    predicate Init(c: Constants, v: Variables)
    {
        && v.decision.None?
    }

    // Protocol steps. Define an action predicate for each step of the protocol
    // that participant can take.
    predicate Vote(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && msgOps.recv.Some?
        && var recvMsg := msgOps.recv.value;
        && recvMsg.VoteReqMsg?
        && msgOps.send == Msg_Option.Some(VoteMsg(c.hostId, c.preference))
        // Infer Abort decision if we're voting No
        && v'.decision == if c.preference.No? then Decision_Option.Some(Abort) else v.decision
    }

    predicate LearnDecision(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && msgOps.recv.Some?
        && var recvMsg := msgOps.recv.value;
        && recvMsg.DecisionMsg?
        && v'.decision == Decision_Option.Some(recvMsg.decision)
        && msgOps.send.None?
    }

    // JayNF
    datatype Step =
        | VoteStep
        | LearnDecisionStep

    predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
    {
        match step
            case VoteStep => Vote(c, v, v', msgOps)
            case LearnDecisionStep => LearnDecision(c, v, v', msgOps)
    }

    predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists step :: NextStep(c, v, v', step, msgOps)
    }
}

// We define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
// This definition is given to you to clarify how the two protocol roles above
// are pulled together into the ultimate distributed system.
module Host {
    import opened Library
    import opened CommitTypes
    import opened Types
    import CoordinatorHost
    import ParticipantHost

    datatype Constants =
        | CoordinatorConstants(coordinator: CoordinatorHost.Constants)
        | ParticipantConstants(participant: ParticipantHost.Constants)

    datatype Variables =
        | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
        | ParticipantVariables(participant: ParticipantHost.Variables)

    predicate WF(c: Constants, v: Variables) {
        && (v.CoordinatorVariables? <==> c.CoordinatorConstants?) // types of c & v agree
        // subtype WF satisfied
        && (match c
                    case CoordinatorConstants(_) => CoordinatorHost.WF(c.coordinator, v.coordinator)
                    case ParticipantConstants(_) => true
                )
    }


    // What property must be true of any group of hosts to run the protocol?
    // Generic DistributedSystem module calls back into this predicate to ensure
    // that it has a well-formed *group* of hosts.
    predicate GroupWFConstants(grp_c: seq<Constants>)
    {
        // There must at least be a coordinator
        && 0 < |grp_c|
        // Last host is a coordinator
        && Last(grp_c).CoordinatorConstants?
        // All the others are participants
        && (forall hostid:HostId | hostid < |grp_c|-1 :: grp_c[hostid].ParticipantConstants?)
        // The coordinator's constants must correctly account for the number of participants
        && CoordinatorHost.ConstantsValidForGroup(Last(grp_c).coordinator, |grp_c|-1)
        // The participants's constants must match their group positions.
        // (Actually, they just need to be distinct from one another so we get
        // non-conflicting votes, but this is an easy way to express that property.)
        && (forall hostid:HostId | hostid < |grp_c|-1
                :: ParticipantHost.ConstantsValidForGroup(grp_c[hostid].participant, hostid))
    }

    predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        && GroupWFConstants(grp_c)
        // Variables size matches group size defined by grp_c
        && |grp_v| == |grp_c|
        // Each host is well-formed
        && (forall hostid:HostId | hostid < |grp_c| :: WF(grp_c[hostid], grp_v[hostid]))
    }

    // Generic DistributedSystem module calls back into this predicate to give
    // the protocol an opportunity to set up constraints across the various
    // hosts.    Protocol requires one coordinator and the rest participants;
    // coordinator must know how many participants, and participants must know
    // own ids.
    predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        // constants & variables are well-formed (same number of host slots as constants expect)
        && GroupWF(grp_c, grp_v)
        // Coordinator is initialized to know about the N-1 participants.
        && CoordinatorHost.Init(Last(grp_c).coordinator, Last(grp_v).coordinator)
        // Participants initted with their ids.
        && (forall hostid:HostId | hostid < |grp_c|-1 ::
                ParticipantHost.Init(grp_c[hostid].participant, grp_v[hostid].participant)
            )
    }

    // Dispatch Next to appropriate underlying implementation.
    predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && WF(c, v)
        && WF(c, v')
        && (match c
            case CoordinatorConstants(_) => CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
            case ParticipantConstants(_) => ParticipantHost.Next(c.participant, v.participant, v'.participant, msgOps)
            )
    }
}

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
// This definition is given to you because it's a common assumption you can
// reuse. Someday you might decide to assume a different network model (e.g.
// reliable or at-most-once delivery), but this is a good place to start.
module Network {
    import opened CommitTypes
    import opened Types

    datatype Constants = Constants    // no constants for network

    // Network state is the set of messages ever sent. Once sent, we'll
    // allow it to be delivered over and over.
    // (We don't have packet headers, so duplication, besides being realistic,
    // also doubles as how multiple parties can hear the message.)
    datatype Variables = Variables(sentMsgs:set<Message>)

    predicate Init(c: Constants, v: Variables)
    {
        && v.sentMsgs == {}
    }

    predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        // Only allow receipt of a message if we've seen it has been sent.
        && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
        // Record the sent message, if there was one.
        && v'.sentMsgs ==
            v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
    }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
// This is given to you; it can be reused for just about any shared-nothing-concurrency
// protocol model.
module DistributedSystem {
    import opened Library
    import opened CommitTypes
    import opened Types
    import Network
    import Host
    import CoordinatorHost
    import ParticipantHost

    datatype Constants = Constants(
        hosts: seq<Host.Constants>,
        network: Network.Constants)
    
    predicate WF_Constants(c:Constants) {
        Host.GroupWFConstants(c.hosts)
    }
    predicate ValidHostId(c:Constants, id: HostId) {
        id < |c.hosts|
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        network: Network.Variables)

    predicate WF_Variables(c: Constants, v:Variables) {
        && WF_Constants(c)
        && Host.GroupWF(c.hosts, v.hosts)
    }

    predicate Init(c: Constants, v: Variables)
    {
        && WF_Variables(c, v)
        && Host.GroupInit(c.hosts, v.hosts)
        && Network.Init(c.network, v.network)
    }

    predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
    {
        && WF_Variables(c, v)
        && WF_Variables(c, v')
        && ValidHostId(c, hostid)
        && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
        // all other hosts UNCHANGED
        && (forall otherHost:nat | ValidHostId(c, otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
    }

    // JayNF is pretty simple as there's only a single action disjunct
    datatype Step =
        | HostActionStep(hostid: HostId, msgOps: MessageOps)

    predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
    {
        && HostAction(c, v, v', step.hostid, step.msgOps)
        // network agrees recv has been sent and records sent
        && Network.Next(c.network, v.network, v'.network, step.msgOps)
    }

    predicate Next(c: Constants, v: Variables, v': Variables)
    {
        exists step :: NextStep(c, v, v', step)
    }
}

module Obligations {
    import opened CommitTypes
    import opened Types
    import opened Library
    import opened DistributedSystem

    // Here are some handy accessor functions for dereferencing the coordinator
    // and the participants out of the sequence in Hosts.
    function CoordinatorConstants(c: Constants) : CoordinatorHost.Constants
        requires DistributedSystem.WF_Constants(c)
    {
        Last(c.hosts).coordinator
    }

    function CoordinatorVars(c: Constants, v: Variables) : CoordinatorHost.Variables
        requires WF_Variables(c, v)
    {
        Last(v.hosts).coordinator
    }

    predicate ValidParticipantId(c: Constants, hostid: HostId)
    {
        hostid < |c.hosts|-1
    }

    function ParticipantConstants(c: Constants, hostid: HostId) : ParticipantHost.Constants
        requires DistributedSystem.WF_Constants(c)
        requires ValidParticipantId(c, hostid)
    {
        c.hosts[hostid].participant
    }

    function ParticipantVars(c: Constants, v: Variables, hostid: HostId) : ParticipantHost.Variables
        requires WF_Variables(c, v)
        requires ValidParticipantId(c, hostid)
    {
        v.hosts[hostid].participant
    }

    predicate AllWithDecisionAgreeWithThisOne(c: Constants, v: Variables, decision: Decision)
        requires WF_Variables(c, v)
        // I pulled this conjunction into a named predicate because Dafny warned of
        // no trigger for the exists.
    {
        && (CoordinatorVars(c, v).decision.Some? ==> CoordinatorVars(c, v).decision.value == decision)
        && (forall hostid:HostId
        | ValidParticipantId(c, hostid) && ParticipantVars(c, v, hostid).decision.Some?
        :: ParticipantVars(c, v, hostid).decision.value == decision)
    }

    // AC-1: All processes that reach a decision reach the same one.
    predicate SafetyAC1(c: Constants, v: Variables)
        requires WF_Variables(c, v)
    {
        // All hosts that reach a decision reach the same one
        || AllWithDecisionAgreeWithThisOne(c, v, Commit)
        || AllWithDecisionAgreeWithThisOne(c, v, Abort)
    }

    // AC2 is sort of a history predicate; we're going to ignore it.

    // AC-3: The Commit decision can only be reached if all processes prefer Yes.
    predicate SafetyAC3(c: Constants, v: Variables)
        requires WF_Variables(c, v)
    {
        && (exists hostid:HostId
        :: ValidParticipantId(c, hostid) && ParticipantConstants(c, hostid).preference.No?)
        ==> AllWithDecisionAgreeWithThisOne(c, v, Abort)
    }

    // AC-4: If all processes prefer Yes, then the decision must be Commit.
    predicate SafetyAC4(c: Constants, v: Variables)
        requires WF_Variables(c, v)
    {
        && (forall hostid:HostId
            | ValidParticipantId(c, hostid) :: ParticipantConstants(c, hostid).preference.Yes?)
        ==> AllWithDecisionAgreeWithThisOne(c, v, Commit)
    }

    // AC5 is a liveness proprety, we're definitely going to ignore it.

    //#instructor Player 1
    predicate Safety(c: Constants, v: Variables)
        requires WF_Variables(c, v)
    {
        && SafetyAC1(c, v)
        && SafetyAC3(c, v)
        && SafetyAC4(c, v)
    }
}

/**
tla_Init == /\ tla_c \in DistributedSystem_Constants 
            /\ tla_s \in DistributedSystem_Variables 
            /\ DistributedSystem_Init(tla_c, tla_s)

tla_Next == /\ tla_s' \in DistributedSystem_Variables 
            /\ DistributedSystem_Next(tla_c, tla_s, tla_s')

tla_Spec == tla_Init /\ [][tla_Next]_(tla_s)

tla_Safety == Obligations_Safety(tla_c, tla_s) \* User input


------------------------------ MODULE MCtwoPC ------------------------------
EXTENDS twoPC

MC_Int == 0..2
MC_Nat == 0..2

p0 ==  [type |-> "ParticipantHost_Constants", hostId |-> 0, preference |-> [type |-> "Yes"]]
c ==  [type |-> "CoordinatorHost_Constants", participantCount |-> 1]

p0_host == [type |-> "ParticipantConstants", participant |-> p0]
c_host == [type |-> "CoordinatorConstants", coordinator |-> c]
net == [type |-> "Network_Constants"]

ds == [type |-> "DistributedSystem_Constants", hosts |-> <<p0_host, c_host>>, network |-> net]


=============================================================================
**/