open Project_Sigs


pred addPhoto[u1, u2: User, p: Photo] {
	u2.owns = u1.owns + p
	u2.friends = u1. friends 
	u2.has = u1.has
}



