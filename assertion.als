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


assert AssertionAddPhoto {
	all s1,s2: Nicebook, u: User, p:Photo | s1 != s2 and
		niceBookInvariants[s1] and addPhoto[s1,s2,u,p] implies niceBookInvariants[s2] 
}

check AssertionAddPhoto for 5 but exactly 2 Nicebook


 assert AssertionRemovePhoto {
 	all s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and removePhoto[s1,s2,u1, u2,p, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionRemovePhoto for 5 but exactly 2 Nicebook



 assert AssertionPublish {
 	all s1,s2: Nicebook, u1: User, p:Photo | s1 != s2 and
 		niceBookInvariants[s1] and publish[s1,s2,u1,p] implies niceBookInvariants[s2]
 }
 check AssertionPublish for 5 but exactly 2 Nicebook


 assert AssertionAddCommentForSameUser {
 		all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 			s1 != s2 and
			u1 = u3 and
	 		niceBookInvariants[s1] and 
	 		addCommentForSelf[s1, s2, c1,c,u1,u3]
	 		implies niceBookInvariants[s2]
 }
 check AssertionAddCommentForSameUser for 5 but exactly 2 Nicebook

 assert AssertionAddCommentForDifferentUser {
 		all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 			s1 != s2 and
			u1 != u3 and
	 		niceBookInvariants[s1] and 
	 		addCommentForDifferentUser[s1, s2, c1,c,u1,u3]
	 		implies niceBookInvariants[s2]
 }
 check AssertionAddCommentForDifferentUser for 5 but exactly 2 Nicebook

 assert AssertionAddComment {
 		all s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 			s1 != s2 and
	 		niceBookInvariants[s1] and 
	 		addComment[s1, s2, c1,c,u1,u3]
	 		implies niceBookInvariants[s2]
 }
 check AssertionAddComment for 5 but exactly 2 Nicebook



 assert AssertionShare{
		all s1,s2: Nicebook,u1,u2: User, p:Photo | 
			s1 != s2 and
			niceBookInvariants[s1] and 
			share[s1, s2, u1,u2,p]
			implies niceBookInvariants[s2]
 }
 check AssertionShare for 5 but exactly 2 Nicebook



 assert AssertionUnpublishPhoto {
 	all s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishPhoto[s1,s2,u1, u2,p, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionUnpublishPhoto for 5 but exactly 2 Nicebook



 assert AssertionUnpublishComment {
 	all s1,s2: Nicebook, u1, u2: User, c:Comment, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishComment[s1,s2,u1, u2,c, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionUnpublishComment for 5 but exactly 2 Nicebook


 assert AssertionUnpublish {
 	all s1,s2: Nicebook, u1, u2: User, c:Content, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublish[s1,s2,u1, u2,c, w1, w2] implies niceBookInvariants[s2]
 }
 check AssertionUnpublish for 5 but exactly 2 Nicebook

