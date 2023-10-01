open Project_Sigs as S
open invariants as I
open operations as O




//
//run GenerateAddPhotoValidInstance {
//	some s1,s2: Nicebook, u: User, p:Photo | s1 != s2 and
//		niceBookInvariants[s1] and addPhoto[s1,s2,u,p] and niceBookInvariants[s2]
//} for 5 but exactly 2 Nicebook, exactly 3 User

run GenerateRemovePhotoValidInstance {
	some s1,s2: Nicebook, u: User, p:Photo | s1 != s2 and
		niceBookInvariants[s1] and removePhoto[s1,s2,u,p] and niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook, exactly 4 User, exactly 4 Comment

//run GenerateValidInstance{
//	all s: Nicebook | niceBookInvariants[s]	
//} for 5 but exactly 1 Nicebook, exactly 3 Comment
