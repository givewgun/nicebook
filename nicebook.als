open Project_Sigs as S
open invariants as I
open operations as O




run GenerateAddPhotoValidInstance {
	some s1,s2: Nicebook, u: User, p:Photo | s1 != s2 and
		niceBookInvariants[s1] and addPhoto[s1,s2,u,p] and niceBookInvariants[s2]
} for 5 but exactly 2 Nicebook, exactly 3 User


 run GenerateRemovePhotoValidInstance {
 	some s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and removePhoto[s1,s2,u1, u2,p, w1, w2] and niceBookInvariants[s2]
 } for 13 but exactly 2 Nicebook, exactly 4 Comment, exactly 5 User



 run GeneratePublishValidInstance {
 	some s1,s2: Nicebook, u1: User, p:Photo| s1 != s2 and
 		niceBookInvariants[s1] and publish[s1,s2,u1,p] and niceBookInvariants[s2]
 } for 5 but exactly 2 Nicebook, exactly 3 User, exactly 2 Comment



 run GenerateAddCommentValidInstance {
 	some s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 		s1 != s2 and
 		niceBookInvariants[s1] and 
 		addComment[s1, s2, c1,c,u1,u3]
 		and niceBookInvariants[s2]
 } for 5 but exactly 2 Nicebook

 run GenerateAddCommentValidInstanceDiffUser {
 	some s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 		s1 != s2 and
		u1 != u3 and
 		niceBookInvariants[s1] and 
 		addCommentForDifferentUser[s1, s2, c1,c,u1,u3]
 		and niceBookInvariants[s2]
 } for 5 but exactly 2 Nicebook

 run GenerateAddCommentValidInstanceSameUser {
 	some s1,s2: Nicebook,u1,u3: User, c1:Content, c:Comment | 
 		s1 != s2 and
		u1 = u3 and
 		niceBookInvariants[s1] and 
 		addCommentForSelf[s1, s2, c1,c,u1,u3]
 		and niceBookInvariants[s2]
 } for 5 but exactly 2 Nicebook


run GenerateShareValidInstance {
	some s1,s2: Nicebook,u1,u2: User, p:Photo | 
		s1 != s2 and
		niceBookInvariants[s1] and 
		share[s1, s2, u1,u2,p]
		and niceBookInvariants[s2]
} for 7 but exactly 2 Nicebook, exactly 5 User


 run GenerateUnpublishPhotoValidInstance {
 	some s1,s2: Nicebook, u1, u2: User, p:Photo, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishPhoto[s1,s2,u1, u2,p, w1, w2] and niceBookInvariants[s2]
 } for 10 but exactly 2 Nicebook, exactly 3 Comment, exactly 3 User


 run GenerateUnpublishCommentValidInstance {
 	some s1,s2: Nicebook, u1, u2: User, c:Comment, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublishComment[s1,s2,u1, u2,c, w1, w2] and niceBookInvariants[s2]
 } for 5 but exactly 2 Nicebook, exactly 2 Comment



 run GenerateUnpublishValidInstance {
 	some s1,s2: Nicebook, u1, u2: User, c:Content, w1, w2:Wall | s1 != s2 and
 		niceBookInvariants[s1] and unpublish[s1,s2,u1, u2,c, w1, w2] and niceBookInvariants[s2]
 } for 5 but exactly 2 Nicebook, exactly 2 Comment



 run GenerateValidInstance {
 	all s: Nicebook | niceBookInvariants[s]
 } for 5 but exactly 2 Nicebook, exactly 3 User
