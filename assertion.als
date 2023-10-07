open Project_Sigs as S
open invariants as I
open operations as O


//initial states
sig Init in Nicebook {}{
	//no users
	no users
}

assert InitSatisfiesInvariant {
	all gi : Init | niceBookInvariants[gi]        // base case
}
check InitSatisfiesInvariant for 5


assert AssertionAddPhotoSatisfiesInvariant {
	all s1,s2: Nicebook, u: User, p:Photo | s1 != s2 and
		niceBookInvariants[s1] and addPhoto[s1,s2,u,p] implies niceBookInvariants[s2] 
}

check AssertionAddPhotoSatisfiesInvariant for 5 but exactly 2 Nicebook


 assert AssertionRemovePhotoSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and removePhoto[s1,s2,u1, u2,p, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionRemovePhotoSatisfiesInvariant for 5 but exactly 2 Nicebook



 assert AssertionPublishSatisfiesInvariant {
 	all s1,s2: Nicebook, u1: User, p:Photo | s1 != s2 and
 		niceBookInvariants[s1] and publish[s1,s2,u1,p] implies niceBookInvariants[s2]
 }
 check AssertionPublishSatisfiesInvariant for 5 but exactly 2 Nicebook


 assert AssertionAddCommentForSameUserSatisfiesInvariant {
 		all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 			s1 != s2 and
			u1 = u3 and
	 		niceBookInvariants[s1] and 
	 		addCommentForSelf[s1, s2, c1,c,u1,u3]
	 		implies niceBookInvariants[s2]
 }
 check AssertionAddCommentForSameUserSatisfiesInvariant for 5 but exactly 2 Nicebook

 assert AssertionAddCommentForDifferentUserSatisfiesInvariant {
 		all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 			s1 != s2 and
			u1 != u3 and
	 		niceBookInvariants[s1] and 
	 		addCommentForDifferentUser[s1, s2, c1,c,u1,u3]
	 		implies niceBookInvariants[s2]
 }
 check AssertionAddCommentForDifferentUserSatisfiesInvariant for 5 but exactly 2 Nicebook

 assert AssertionAddCommentSatisfiesInvariant {
 		all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 			s1 != s2 and
	 		niceBookInvariants[s1] and 
	 		addComment[s1, s2, c1,c,u1,u3]
	 		implies niceBookInvariants[s2]
 }
 check AssertionAddCommentSatisfiesInvariant for 5 but exactly 2 Nicebook



 assert AssertionShareSatisfiesInvariant{
		all s1,s2: Nicebook,u1,u2: User, p:Photo | 
			s1 != s2 and
			niceBookInvariants[s1] and 
			share[s1, s2, u1,u2,p]
			implies niceBookInvariants[s2]
 }
 check AssertionShareSatisfiesInvariant for 5 but exactly 2 Nicebook



 assert AssertionUnpublishPhotoSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishPhoto[s1,s2,u1, u2,p, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionUnpublishPhotoSatisfiesInvariant for 5 but exactly 2 Nicebook



 assert AssertionUnpublishCommentSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, c:Comment, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishComment[s1,s2,u1, u2,c, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionUnpublishCommentSatisfiesInvariant for 5 but exactly 2 Nicebook


 assert AssertionUnpublishSatisfiesInvariant {
 	all s1,s2: Nicebook, u1, u2: User, c:Content, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublish[s1,s2,u1, u2,c, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionUnpublishSatisfiesInvariant for 5 but exactly 2 Nicebook

