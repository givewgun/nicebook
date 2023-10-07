open Project_Sigs as S
open invariants as I
open operations as O

// This command checks the possibility of adding a photo to the Nicebook state in a valid manner.
run GenerateAddPhotoValidInstance {
	// It specifies an old state s1 and a new state s2, a user u, and a photo p.
	some s1,s2: Nicebook, u: User, p:Photo | s1 != s2 and
		// Ensures that the previous state satisfies the invariants.
		niceBookInvariants[s1] and 
		// Checks the addPhoto operation between the two states.
		addPhoto[s1,s2,u,p] and 
		// Ensures that the new state also satisfies the invariants.
		niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook, exactly 3 User

// This command checks the possibility of removing a photo from the Nicebook state while still being valid.
run GenerateRemovePhotoValidInstance {
	// It includes two states, two users (one for ownership and one for operation), a photo, and walls related to the users.
	some s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
		niceBookInvariants[s1] and 
		removePhoto[s1,s2,u1, u2,p, w1, w2] and 
		niceBookInvariants[s2]
} for 13 but exactly 2 Nicebook, exactly 4 Comment, exactly 5 User

// This command tests the valid publishing of a photo to Nicebook.
run GeneratePublishValidInstance {
	some s1,s2: Nicebook, u1: User, p:Photo| s1 != s2 and
		niceBookInvariants[s1] and 
		publish[s1,s2,u1,p] and 
		niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook, exactly 3 User, exactly 2 Comment

// This command checks if a user can add a comment for themselves in a valid state.
run GenerateAddCommentValidInstanceSameUser {
	some s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
		s1 != s2 and
		u1 = u3 and
		niceBookInvariants[s1] and 
		addCommentForSelf[s1, s2, c1,c,u1,u3] and 
		niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook

// This command checks if a user can add a comment for a different user while the state remains valid.
run GenerateAddCommentValidInstanceDiffUser {
	some s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
		s1 != s2 and
		u1 != u3 and
		niceBookInvariants[s1] and 
		addCommentForDifferentUser[s1, s2, c1,c,u1,u3] and 
		niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook

// This command checks the valid addition of any comment in the Nicebook state.
run GenerateAddCommentValidInstance {
	some s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
		s1 != s2 and
		niceBookInvariants[s1] and 
		addComment[s1, s2, c1,c,u1,u3] and 
		niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook

// This command checks the sharing of a photo in a valid state of Nicebook.
run GenerateShareValidInstance {
	some s1,s2: Nicebook,u1,u2: User, p:Photo | 
		s1 != s2 and
		niceBookInvariants[s1] and 
		share[s1, s2, u1,u2,p] and 
		niceBookInvariants[s2]
} for 7 but exactly 2 Nicebook, exactly 5 User

// This command verifies that a photo can be unpublished in a Nicebook valid state.
run GenerateUnpublishPhotoValidInstance {
	some s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
		niceBookInvariants[s1] and 
		unpublishPhoto[s1,s2,u1, u2,p, w1, w2] and 
		niceBookInvariants[s2]
} for 10 but exactly 2 Nicebook, exactly 3 Comment, exactly 3 User

// This command checks the unpublishing of a comment in a Nicebook valid state.
run GenerateUnpublishCommentValidInstance {
	some s1,s2: Nicebook, u1, u2: User, c:Comment, w1, w2:Wall | s1 != s2 and
		niceBookInvariants[s1] and 
		unpublishComment[s1,s2,u1, u2,c, w1, w2] and 
		niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook, exactly 2 Comment

// This command checks the unpublishing of any content in a Nicebook valid state.
run GenerateUnpublishValidInstance {
	some s1,s2: Nicebook, u1, u2: User, c:Content, w1, w2:Wall | s1 != s2 and
		niceBookInvariants[s1] and 
		unpublish[s1,s2,u1, u2,c, w1, w2] and 
		niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook, exactly 2 Comment

// This command validates the general invariants for the Nicebook state.
run GenerateValidInstance {
	all s: Nicebook | niceBookInvariants[s]
} for 5 but exactly 2 Nicebook, exactly 3 User
