../../../lib/ActLib.vo ../../../lib/ActLib.glob ../../../lib/ActLib.v.beautified ../../../lib/ActLib.required_vo: ../../../lib/ActLib.v 
../../../lib/ActLib.vos ../../../lib/ActLib.vok ../../../lib/ActLib.required_vos: ../../../lib/ActLib.v 
StateMachine.vo StateMachine.glob StateMachine.v.beautified StateMachine.required_vo: StateMachine.v ../../../lib/ActLib.vo
StateMachine.vos StateMachine.vok StateMachine.required_vos: StateMachine.v ../../../lib/ActLib.vos
Theory.vo Theory.glob Theory.v.beautified Theory.required_vo: Theory.v StateMachine.vo ../../../lib/ActLib.vo
Theory.vos Theory.vok Theory.required_vos: Theory.v StateMachine.vos ../../../lib/ActLib.vos
