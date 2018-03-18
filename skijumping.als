open general

//// Ski Jumping Discipline
sig SkiJumpingDiscipline extends Discipline {
	individualEvent: one SkiJumpingIndividualEvent,
	teamEvent: one SkiJumpingTeamEvent
}

fact sDisciplineFacts {
	// Override Discipline.events.
	all sDiscipline: SkiJumpingDiscipline | sDiscipline.events
		= sDiscipline.individualEvent + sDiscipline.teamEvent
}

//// Ski Jumping Event
abstract sig SkiJumpingEvent extends Event {
	qualifyingPhase: one SkiJumpingQualifyingPhase,
	finalPhase: one SkiJumpingFinalPhase
}
sig SkiJumpingIndividualEvent extends SkiJumpingEvent { }
sig SkiJumpingTeamEvent extends SkiJumpingEvent { }

fact sEventFacts {
	// Override Event.phases.
	all sEvent: SkiJumpingEvent | sEvent.phases 
		= sEvent.qualifyingPhase + sEvent.finalPhase
	// Sport specific constraint.
	all discipline: Discipline, event: discipline.events |
		event in SkiJumpingEvent iff discipline in SkiJumpingDiscipline
}

//// Ski Jumping Phase
abstract sig SkiJumpingPhase extends Phase { }
sig SkiJumpingQualifyingPhase extends SkiJumpingPhase {
	roundOne: one SkiJumpingPerformanceBigRound
}
sig SkiJumpingFinalPhase extends SkiJumpingPhase {
	roundOne: one SkiJumpingPerformanceBigRound,
	roundTwo: one SkiJumpingPerformanceSmallRound
}

fact sPhaseFacts {
	// Override Phase.performances.
	all sQPhase: SkiJumpingQualifyingPhase | sQPhase.performances = sQPhase.roundOne
	all sFPhase: SkiJumpingFinalPhase | sFPhase.performances = sFPhase.roundOne + sFPhase.roundTwo
	// Sport Specific Constraint.
	all event: Event, phase: event.phases | phase in SkiJumpingPhase 
		iff event in SkiJumpingEvent
}

//// Ski Jumping Performance
abstract sig SkiJumpingPerformance extends Performance { }
sig SkiJumpingPerformanceBigRound extends SkiJumpingPerformance { }
sig SkiJumpingPerformanceSmallRound extends SkiJumpingPerformance { }

fact sPerformanceFacts {
	// Override Performance.teams.
	all sPerformance: SkiJumpingPerformance | sPerformance.teams in SkiJumpingTeam
	// Sport Specific Constraint.
	all phase: Phase, performance: phase.performances | performance in SkiJumpingPerformance
		iff phase in SkiJumpingPhase
	// Override Performance.score.
	all sPerformance: SkiJumpingPerformance | sPerformance.score in SkiJumpingScore
	// Big Round consists of 50 teams.
	all sBig: SkiJumpingPerformanceBigRound | #sBig.teams = 50
	// Small Round consists of 30 teams.
	all sSmall: SkiJumpingPerformanceSmallRound | #sSmall.teams = 30
}

//// Ski Jumping Team
abstract sig SkiJumpingTeam extends Team { }
sig SkiJumpingIndividualTeam extends SkiJumpingTeam { }
sig SkiJumpingGroupTeam extends SkiJumpingTeam { }

fact sTeamFacts {
	// Only consider male athletes participate in this sport.
	all sTeam: SkiJumpingTeam | sTeam.athletes in MaleAthlete
	// Individual Team consists only one athlete.
	all sITeam: SkiJumpingIndividualTeam | #sITeam.athletes = 1
	// GroupTeam consists four athletes.
	all sGTeam: SkiJumpingGroupTeam | #sGTeam.athletes = 4
	// Only Individual Teams can participate in Individual Event.
	all sIEvent: SkiJumpingIndividualEvent | sIEvent.teams in SkiJumpingIndividualTeam
	// Only Group Teams can participate in Team Event.
	all sTEvent: SkiJumpingTeamEvent | sTEvent.teams in SkiJumpingGroupTeam
}

//// Ski Jumping Score
sig SkiJumpingScore extends Score {
	distances: SkiJumpingTeam -> one Float,
	points: SkiJumpingTeam -> one Float,
	total: SkiJumpingTeam -> one Float
}

fact sScoreFacts {
	
}

sig Float { }

run { #SkiJumpingDiscipline = 1 } for 10
