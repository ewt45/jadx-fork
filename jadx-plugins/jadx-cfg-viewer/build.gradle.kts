plugins {
//	id("jadx-library")
	`java-library`
}

java {
	sourceCompatibility = JavaVersion.VERSION_11
	targetCompatibility = JavaVersion.VERSION_11
}

dependencies {
	compileOnly(project(":jadx-core"))
	compileOnly(project(":jadx-gui"))
	compileOnly("org.slf4j:slf4j-api:2.0.17")
	// 来自 jadx-gui
	compileOnly("com.fifesoft:rsyntaxtextarea:3.6.0")
	compileOnly("com.formdev:flatlaf-extras:3.7")

	implementation("org.piccolo2d:piccolo2d-core:3.0.1")
	implementation("org.piccolo2d:piccolo2d-extras:3.0.1")
}
