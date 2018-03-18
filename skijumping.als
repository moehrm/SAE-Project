open general

//// Ski Jumping Discipline
sig SkiJumpingDiscipline extends Discipline { }

//// Ski Jumping Event
abstract sig SkiJumpingEvent extends Event { }
sig SkiJumpingIndividualEvent extends SkiJumpingEvent { }
sig SkiJumpingTeamEvent extends SkiJumpingEvent { }

//// Ski Jumping Phase
abstract sig SkiJumpingPhase extends Phase { }
sig SkiJumpingQualifyingPhase extends SkiJumpingPhase { }
sig SkiJumpingFinalPhase extends SkiJumpingPhase { }

//// Ski Jumping Performance
abstract sig SkiJumpingPerformance extends Performance { }
sig SkiJumpingPerformanceBigRound extends SkiJumpingPerformance { }
sig SkiJumpingPerformanceSmallRound extends SkiJumpingPerformance { }

fact skiJumpingPerformanceFacts {
	
}

//// Ski Jumping Team
abstract sig SkiJumpingTeam extends Team { }
sig SkiJumpingIndividualTeam extends SkiJumpingTeam { }
sig SkiJumpingGroupTeam extends SkiJumpingTeam { }

fact skiJumpingTeamFacts {
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


run {} for 5
