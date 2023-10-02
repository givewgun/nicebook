open Project_Sigs


pred addPhoto[s1, s2: Nicebook, u1: User, p: Photo] {
	//pre condition 
	//true
	//post condition
	//add photo to user owns content
	some u2: User {
		u2.owns = u1.owns + p
		u2.friends = u1. friends 
		u2.has = u1.has
		s2.users = s1.users + u2 -u1
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
	u2.owns = u1.owns - p
	u2.friends = u1.friends 
	
	//Ensure the relationship between User and Wall
	u1.has = w1
	u2.has = w2
	
	//remove photo from owner wall
	w2.contains = w1.contains - p 
	
	s2.users = s1.users + u2 - u1
}


pred publish[s1, s2: Nicebook, u1, u2: User, p: Photo, w1, w2: Wall] {
	//pre condition 
	//photo must be owned by user (u1)
	p in u1.owns
	//photo must not already be on user (u1) wall
	p not in u1.has.contains
	
	// Ensure w1 and w2 are distinct
	w1 != w2
	
	//post condition

	//add photo from owner wall
	w2.contains = w1.contains + p 
	//new user state
	u2.owns = u1.owns
	u2.friends = u1.friends 
	//Ensure the relationship between User and Wall
	u1.has = w1
	u2.has = w2

	//add new user to new state
	s2.users = s1.users + u2 - u1

}

pred addComment[s1, s2: Nicebook, c1:Content ,c: Comment, u1,u3:User]{
	//pre-condition
	//owner must be in the old state
	u1 in s1.users
	//user should own that content
	(u3 in (u1).friends and c1.commentPrivacy != OnlyMe and c1.viewPrivacy!=OnlyMe)
	or (u3 in (u1).friends.friends and (c1.viewPrivacy=Everyone or c1.viewPrivacy=FriendsOfFriends)
	and  (c1.commentPrivacy=Everyone  or c1.commentPrivacy=FriendsOfFriends))
	//post-condition
	some u2, u4: User{
		some w2:Wall{
			//preconditon for new user
			u2 != u4
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
			//frame condtion
			u2.friends = u1.friends
			u2.owns = u1.owns
		}
		s2.users = s1.users - u1 + u2 - u3 + u4
	}

}
