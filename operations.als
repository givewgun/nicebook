open Project_Sigs


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


pred removeCommentIfAttachTo[s1, s2: Nicebook, u3: User, p: Photo]{
	//precondition 
	//u1 in old state
	u3 in s1.users
	//photo in old state
	p in s1.users.owns

	some u4: User {
		u4.owns = u3.owns - ^attachedTo.p
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

pred addComment[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User]{
	//pre-condition
	//owner must be in the old state
	u1 in s1.users
	//commenter must be in the old state
	u3 in s1.users
	//comment must not exist in the old state
	c not in s1.users.owns
	//comment must not be attached to the content
	c not in ^attachedTo.c1
	//user should own that content
	(u3 in (u1).friends and c1.commentPrivacy != OnlyMe and c1.viewPrivacy!=OnlyMe)
	or (u3 in (u1).friends.friends and (c1.viewPrivacy=Everyone or c1.viewPrivacy=FriendsOfFriends)
	and  (c1.commentPrivacy=Everyone  or c1.commentPrivacy=FriendsOfFriends))
	//post-condition
	some u2, u4: User{
		some w2:Wall{
			//comment must not be in the old state of the commenter
                      c not in u3.owns 
			//new commenter state (u4)
			//add comment to new commenter user state
			u4.owns=u3.owns+c
			//frame conditon for u4
			u4.friends = u3.friends
			u4.has = u3.has

			//new content owner state (u2)
			//add new wall state for original content owner
			w2.contains = (u1.has).contains+c
			u2.has = w2
			has.w2 = u2
			//frame condtion
			u2.friends = u1.friends
			u2.owns = u1.owns
		}
		s2.users = s1.users - u1 + u2 - u3 + u4
	}

}


pred share[u1, u2: User, p: Photo, w1, w2:Wall] {
    // pre condition
    // the user owns the content
    p in u1.owns
    // the privacy settings allow the user2 to share the post
    (u2 in u1.friends and p.sharePrivacy != OnlyMe and p.viewPrivacy!=OnlyMe)
    or (u2 in u1.friends.friends and (p.viewPrivacy=Everyone or p.viewPrivacy=FriendsOfFriends)
    and  (p.sharePrivacy=Everyone  or p.sharePrivacy=FriendsOfFriends)) 
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
	(u2 in (u1).friends and p.sharePrivacy != OnlyMe and p.viewPrivacy!=OnlyMe)
	or (u2 in (u1).friends.friends and (p.viewPrivacy=Everyone or p.viewPrivacy=FriendsOfFriends)
	and  (p.sharePrivacy=Everyone  or p.sharePrivacy=FriendsOfFriends))
	//post-condition
	some u3: User{
		some w3:Wall{
			//preconditon for new user
			u2 != u3
			//pre condition for new wall
			w3 != u2.has
			//add photo to new wall
			w3.contains = u2.has.contains + p
			u3.has = w3
			//frame condition
			u3.friends = u2.friends
			u3.owns = u2.owns
		}
		s2.users = s1.users - u2 + u3
	}

}
