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

pred removePhoto[s1, s2: Nicebook, u1: User, p: Photo] {
	//pre condition 
	//photo must be owned by user
	p in u1.owns
	//post condition
	//new user state

	some u2: User {
		//remove photo from user owns content
		u2.owns = u1.owns - p
		//remove photo from owner wall
		u2.has.contains = u1.has.contains - p
		s2.users = s1.users + u2 -u1
		u2.has.contains = u1.has.contains - p

		u2.friends = u1. friends 
		u2.has = u1.has
	}
}

