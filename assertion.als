/*
	Team 10
*/
// Importing necessary modules or signatures, invariants, and operations.
open Project_Sigs as S
open invariants as I
open operations as O

// Signature representing the initial state of the Nicebook.
sig Init in Nicebook {}{
	// Initial state should have no users.
	no users
}

// Assertion to ensure the initial state of the Nicebook adheres to all invariants.
assert InitSatisfiesInvariant {
	// For all initial states, the Nicebook must satisfy all invariants.
	all gi : Init | niceBookInvariants[gi]        // base case
}
check InitSatisfiesInvariant for 5

// Assertion to ensure adding a photo doesn't break any invariants.
assert AssertionAddPhotoSatisfiesInvariant {
	all s1,s2: Nicebook, u: User, p:Photo | s1 != s2 and
		niceBookInvariants[s1] and addPhoto[s1,s2,u,p] implies niceBookInvariants[s2] 
}
check AssertionAddPhotoSatisfiesInvariant for 5 but exactly 2 Nicebook, exactly 2 User 

// Assertion to ensure removing a photo doesn't break any invariants.
assert AssertionRemovePhotoSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and removePhoto[s1,s2,u1, u2,p, w1, w2] implies niceBookInvariants[s2]
}
check AssertionRemovePhotoSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure publishing a photo doesn't break any invariants.
assert AssertionPublishSatisfiesInvariant {
 	all s1,s2: Nicebook, u1: User, p:Photo | s1 != s2 and
 		niceBookInvariants[s1] and publish[s1,s2,u1,p] implies niceBookInvariants[s2]
}
check AssertionPublishSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure adding a comment for the same user doesn't break any invariants.
assert AssertionAddCommentForSameUserSatisfiesInvariant {
	all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
		s1 != s2 and
		u1 = u3 and
		niceBookInvariants[s1] and 
		addCommentForSelf[s1, s2, c1,c,u1,u3]
		implies niceBookInvariants[s2]
}
check AssertionAddCommentForSameUserSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure adding a comment for a different user doesn't break any invariants.
assert AssertionAddCommentForDifferentUserSatisfiesInvariant {
	all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
		s1 != s2 and
		u1 != u3 and
		niceBookInvariants[s1] and 
		addCommentForDifferentUser[s1, s2, c1,c,u1,u3]
		implies niceBookInvariants[s2]
}
check AssertionAddCommentForDifferentUserSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure adding any comment doesn't break any invariants.
assert AssertionAddCommentSatisfiesInvariant {
	all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
		s1 != s2 and
		niceBookInvariants[s1] and 
		addComment[s1, s2, c1,c,u1,u3]
		implies niceBookInvariants[s2]
}
check AssertionAddCommentSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure sharing content doesn't break any invariants.
assert AssertionShareSatisfiesInvariant{
	all s1,s2: Nicebook,u1,u2: User, p:Photo | 
		s1 != s2 and
		niceBookInvariants[s1] and 
		share[s1, s2, u1,u2,p]
		implies niceBookInvariants[s2]
}
check AssertionShareSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure unpublishing a photo doesn't break any invariants.
assert AssertionUnpublishPhotoSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishPhoto[s1,s2,u1, u2,p, w1, w2] implies niceBookInvariants[s2]
 }
check AssertionUnpublishPhotoSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure unpublishing a comment doesn't break any invariants.
assert AssertionUnpublishCommentSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, c:Comment, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishComment[s1,s2,u1, u2,c, w1, w2] implies niceBookInvariants[s2]
}
check AssertionUnpublishCommentSatisfiesInvariant for 5 but exactly 2 Nicebook

// Assertion to ensure any unpublishing action (for photo or comment) doesn't break any invariants.
assert AssertionUnpublishSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, c:Content, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublish[s1,s2,u1, u2,c, w1, w2] implies niceBookInvariants[s2]
}
check AssertionUnpublishSatisfiesInvariant for 5 but exactly 2 Nicebook

