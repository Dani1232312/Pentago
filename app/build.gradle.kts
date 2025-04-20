plugins {
    // Apply the application plugin to add support for building a CLI application in Java.
    application
    // Apply the Java plugin for standard Java projects
    java
}

repositories {
    // Use Maven Central for resolving dependencies.
    mavenCentral()
}

dependencies {
    // This dependency is used by the application.
    implementation("com.google.guava:guava:31.0.1-jre")  // Updated to Kotlin string syntax

    // Test dependencies
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.8.2")  // JUnit 5 API
    testImplementation("org.junit.jupiter:junit-jupiter-engine:5.8.2")  // JUnit 5 Engine
}

tasks.test {
    useJUnitPlatform()  // JUnit Platform for JUnit 5
}

// Apply a specific Java toolchain to ease working on different environments.
java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(17))  // Java 17 toolchain
    }
}

application {
    // Define the main class for the application.
    mainClass.set("org.example.Pentago")
}
