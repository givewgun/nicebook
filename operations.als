open Project_Sigs
open invariants

pred addPhoto[s1, s2: Nicebook, u1: User, p: Photo] {
	//pre condition 
	//photo not owns by any one in old state
	p not in s1.users.owns
	//true
	//post condition
	//add photo to user owns content
	some u2: User {
		u2.owns = u1.owns + p
		u2.friends = u1. friends 
		u2.has = u1.has
		s2.users = s1.users + u2 -u1
		s2.users.owns = s1.users.owns + p
	}
}

pred removePhoto[s1, s2: Nicebook, u1, u2: User, p: Photo, w1, w2: Wall] {
	//pre condition 
	//photo must be owned by user (u1)
	p in u1.owns

	// Ensure w1 and w2 are distinct
	w1 != w2
	
	//post condition
	//new user state
	u2.owns = u1.owns - p - ^attachedTo.p 
	u2.friends = u1.friends 
	
	//Ensure the relationship between User and Wall
	u1.has = w1
	u2.has = w2

	// all u: User | u in s2.users implies ^attachedTo.p not in u.owns

	// all w: Wall | w in s2.users.has implies ^attachedTo.p not in w.contains
	
	//remove photo and all attached content from owner wall
	w2.contains = w1.contains - p - ^attachedTo.p 

	//ensure comment of u1=2
	^attachedTo.p not in w2.contains
	
	s2.users = s1.users + u2 - u1

	//condition for user with comment attached to this
	all u3: owns.(^attachedTo.p) - u1 | removeCommentIfAttachTo[s1,s2, u3, p]
}


pred removeCommentIfAttachTo[s1, s2: Nicebook, u3: User, c: Content]{
	//precondition 
	//u1 in old state
	u3 in s1.users
	//photo in old state
	c in s1.users.owns

	some u4: User {
		u4.owns = u3.owns - ^attachedTo.c
		u4.has = u3.has

		s2.users = s1.users - u3 + u4
	}
}



pred publish[s1, s2: Nicebook, u1: User, p: Photo] {
	//pre condition 
	//photo must be owned by user (u1)
	p in u1.owns
	//photo must not already be on user (u1) wall
	p not in u1.has.contains

	//post condition
	some u2: User {
		u2 != u1
		some w2: Wall {
			w2 not in u1.has
			//add photo from owner wall
			w2.contains = u1.has.contains + p 
			//set new wall to new user and ensure only new user owns that wall
			u2.has = w2
			has.w2 = u2
		}
		//frame condition for user owns content
		u2.owns = u1.owns
		//frame condition for user friends
		u2.friends = u1.friends 
		
		//update new state with new user
		s2.users = s1.users + u2 - u1
	}

}

pred addCommentForSelf[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User] {
	//pre-condition
	//owner must be in the old state
	u1 in s1.users
	//commenter must be in the old state
	u3 in s1.users
	//same user
	u1 = u3
	//content owned by owner
	c1 in u1.owns
	//comment must not exist in the old state
	c not in s1.users.owns
	// the comment and the peice of content shouldn't be the same 
	c != c1

	//content must be owned in state 1
	//comment must not be cyclic
	(c not in c.^attachedTo) and (c not in ^attachedTo.c)
	//user should own that content
	c1 in s1.users.owns
	//comment must not be cyclic
	(c not in c.^attachedTo) and (c not in ^attachedTo.c)
	//post-condition
	//comment attached to only 1 content
	c.attachedTo = c1
	#(c.attachedTo) = 1
	some u2: User, w2: Wall {
		//create new wall with new comment
		w2.contains = (u1.has).contains+c
		//new comment must be only on new wall
		contains.c = w2
		//add new comemnt to new user ownership
		u2.owns = u1.owns + c
		u2.has = w2
		has.w2 = u2
		//frame condtion
		u2.friends = u1.friends
	
	
	//update new state with new users
	s2.users = s1.users - u1 + u2
	}
}



pred addCommentForDifferentUser[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User] {
	//pre-condition
	//owner must be in the old state
	u1 in s1.users
	//commenter must be in the old state
	u3 in s1.users
//	//different user
//	u1 != u3
	//content owned by owner
	c1 in u1.owns
	//comment must not exist in the old state
	c not in s1.users.owns
	//comment must not be in the old state of the commenter
        c not in u3.owns 
	// the comment and the peice of content shouldn't be the same 
	c != c1

	//content must be owned in state 1
	//comment must not be cyclic
	(c not in c.^attachedTo) and (c not in ^attachedTo.c)
	//user should own that content
	c1 in s1.users.owns
	//comment must not be cyclic
	(c not in c.^attachedTo) and (c not in ^attachedTo.c)
	//privacy
	(u3 in (u1).friends and c1.commentPrivacy != OnlyMe and c1.viewPrivacy!=OnlyMe)
	or (u3 in (u1).friends.friends and (c1.viewPrivacy=Everyone or c1.viewPrivacy=FriendsOfFriends)
	and  (c1.commentPrivacy=Everyone  or c1.commentPrivacy=FriendsOfFriends))
	//post-condition
	//comment attached to only 1 content
	c.attachedTo = c1
	#(c.attachedTo) = 1


	some u2, u4: User{
			some w2:Wall{
				//new commenter state (u4)
				//add comment to new commenter user state
				u4.owns=u3.owns+c
				//frame conditon for u4
				u4.friends = u3.friends
				u4.has = u3.has
	
				//new content owner state (u2)
				//add new wall state for original content owner
				w2.contains = (u1.has).contains+c
				//new comment must be only on new wall
				contains.c = w2
				//set new wall
				u2.has = w2
				has.w2 = u2
				//frame condtion
				u2.friends = u1.friends
				u2.owns = u1.owns
			}
			//update new state with new users
			s2.users = s1.users - u1 + u2 - u3 + u4
		}
}

pred addComment[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User]{
	(u1 = u3)  implies addCommentForSelf[s1,s2,c1,c,u1,u3] else addCommentForDifferentUser[s1,s2,c1,c,u1,u3]
}


pred share[u1, u2: User, p: Photo, w1, w2:Wall] {
    // pre condition
    // the user owns the content
    p in u1.owns
    // the privacy settings allow the user2 to share the post
    (u2 in u1.friends and (owns.p).sharePrivacy != OnlyMe and p.viewPrivacy!=OnlyMe)
    or (u2 in u1.friends.friends and (p.viewPrivacy=Everyone or p.viewPrivacy=FriendsOfFriends)
    and  ((owns.p).sharePrivacy=Everyone  or (owns.p).sharePrivacy=FriendsOfFriends)) 
    // post condition
    // the post should now show up on the users wall
    w2 in u2.has
    w2.contains = w1.contains + p
}


pred share[s1, s2: Nicebook, u1,u2:User,  p:Photo]{
	//pre-condition
	//owner must be in the old state
	u1 in s1.users
	//photo must be owned by u1 (owner)
	 p in u1.owns
	//u2 is different from owner
	u2 != u1
	//user should own that content
	(u2 in (u1).friends and (owns.p).sharePrivacy != OnlyMe and p.viewPrivacy!=OnlyMe)
	or (u2 in (u1).friends.friends and (p.viewPrivacy=Everyone or p.viewPrivacy=FriendsOfFriends)
	and  ((owns.p).sharePrivacy=Everyone  or (owns.p).sharePrivacy=FriendsOfFriends))
	//post-condition
	some u3: User{
		some w3:Wall{
			//preconditon for new user
			u2 != u3
			//pre condition for new wall
			//new wall noi own by old user
			w3 not in u2.has + u1.has
			//add photo to new wall
			w3.contains = u2.has.contains + p
			u3.has = w3
			has.w3 = u3
			//frame condition
			u3.friends = u2.friends
			u3.owns = u2.owns
		}
		s2.users = s1.users - u2 + u3
	}

}


pred unpublishPhoto[s1, s2: Nicebook, u1, u2: User, p: Photo, w1, w2: Wall] {
	//pre condition 
	//photo must be owned by user (u1)
	p in u1.owns

	// Ensure w1 and w2 are distinct
	w1 != w2
	
	//post condition
	//new user state
	u2.owns = u1.owns - ^attachedTo.p 
	u2.friends = u1.friends 
	
	//Ensure the relationship between User and Wall
	u1.has = w1
	u2.has = w2

	// all u: User | u in s2.users implies ^attachedTo.p not in u.owns

	// all w: Wall | w in s2.users.has implies ^attachedTo.p not in w.contains
	
	//remove photo and all attached content from owner wall
	w2.contains = w1.contains - p - ^attachedTo.p 

	//ensure comment of u1=2
	^attachedTo.p not in w2.contains
	
	s2.users = s1.users + u2 - u1

	//condition for user with comment attached to this
	all u3: owns.(^attachedTo.p) - u1 | removeCommentIfAttachTo[s1,s2, u3, p]
}


pred unpublishComment[s1, s2: Nicebook, u1, u2: User, c: Comment, w1, w2: Wall] {
	//pre condition 
	//photo must be owned by user (u1)
	c in u1.owns

	//comment must not be cyclic in s1
	commentNotCyclic[s1]
	//comment must not be cyclic in s1
	commentNotCyclic[s2]


	//user must be in old state
	u1 in s1.users
	u2 not in s1.users

	// Ensure w1 and w2 are distinct
	w1 != w2
	
	//post condition
	//new user state
	u2.owns = u1.owns - c - ^attachedTo.c 
	u2.friends = u1.friends 
	
	//Ensure the relationship between User and Wall
	u1.has = w1
	u2.has = w2
	
	//remove photo and all attached content from owner wall
	w2.contains = w1.contains - c - ^attachedTo.c 

	//ensure comment of u1=2
	^attachedTo.c not in w2.contains
	
	s2.users = s1.users + u2 - u1

	//condition for user with comment attached to this
	all u3: owns.(^attachedTo.c) - u1 | removeCommentIfAttachTo[s1,s2, u3,c]
}
